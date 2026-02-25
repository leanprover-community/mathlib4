#!/usr/bin/env python3
"""Mint a GitHub App installation token using Azure Key Vault signing.

This script is invoked by the local composite action. It builds a JWT for a
GitHub App, signs the JWT digest with an Azure Key Vault key via OIDC-authenticated
REST calls, and exchanges the JWT for an installation access token.
"""

import base64
import hashlib
import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request


class GithubHttpError(Exception):
    """Represents an HTTP error from the GitHub API."""

    def __init__(self, method: str, url: str, status: int, detail: str) -> None:
        super().__init__(f"GitHub API {method} {url} failed: HTTP {status}\n{detail}")
        self.status = status


def fail(message: str) -> None:
    """Print an error and exit with status 1."""

    print(message, file=sys.stderr)
    raise SystemExit(1)


def b64url_encode(raw: bytes) -> str:
    """Return URL-safe base64 without padding."""

    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def b64url_decode(maybe_b64url: str) -> bytes:
    """Decode URL-safe base64 with optional missing padding."""

    padded = maybe_b64url + "=" * ((4 - len(maybe_b64url) % 4) % 4)
    return base64.urlsafe_b64decode(padded.encode("ascii"))


def parse_repositories(raw: str) -> list[str]:
    """Parse comma/newline-delimited repository names."""

    repos: list[str] = []
    for chunk in raw.replace("\n", ",").split(","):
        repo = chunk.strip()
        if repo:
            repos.append(repo)
    return repos


def read_required_env(name: str, label: str) -> str:
    """Read and validate a required action input from the environment."""

    value = os.environ.get(name, "").strip()
    if not value:
        fail(f"{label} is required.")
    return value


def parse_expiration_seconds(raw: str) -> int:
    """Parse and validate JWT expiration seconds."""

    try:
        expiration_seconds = int(raw)
    except ValueError:
        fail(f"jwt-expiration-seconds must be an integer, got: {raw}")
    if expiration_seconds <= 0 or expiration_seconds > 600:
        fail("jwt-expiration-seconds must be between 1 and 600.")
    return expiration_seconds


def get_actions_oidc_token(audience: str) -> str:
    """Fetch a GitHub Actions OIDC token for the configured audience."""

    request_url = os.environ.get("ACTIONS_ID_TOKEN_REQUEST_URL", "").strip()
    request_token = os.environ.get("ACTIONS_ID_TOKEN_REQUEST_TOKEN", "").strip()
    if not request_url or not request_token:
        fail(
            "GitHub OIDC request variables are missing. "
            "Ensure the workflow grants `permissions: id-token: write`."
        )

    parsed = urllib.parse.urlsplit(request_url)
    query_pairs = urllib.parse.parse_qsl(parsed.query, keep_blank_values=True)
    # Audience must match the Entra federated credential configuration.
    query_pairs.append(("audience", audience))
    url_with_audience = urllib.parse.urlunsplit(
        (parsed.scheme, parsed.netloc, parsed.path, urllib.parse.urlencode(query_pairs), parsed.fragment)
    )

    req = urllib.request.Request(url=url_with_audience, method="GET")
    req.add_header("Authorization", f"Bearer {request_token}")
    try:
        with urllib.request.urlopen(req) as resp:
            oidc_response = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as err:
        detail = err.read().decode("utf-8", errors="replace")
        fail(f"Failed to fetch GitHub OIDC token: HTTP {err.code}\n{detail}")
    except urllib.error.URLError as err:
        fail(f"Failed to fetch GitHub OIDC token: {err.reason}")
    except json.JSONDecodeError:
        fail("GitHub OIDC response was not valid JSON.")

    oidc_token = oidc_response.get("value")
    if not isinstance(oidc_token, str) or not oidc_token.strip():
        fail("GitHub OIDC response did not include token in `value`.")
    return oidc_token.strip()


def exchange_oidc_for_keyvault_token(tenant_id: str, client_id: str, oidc_token: str) -> str:
    """Exchange a GitHub OIDC token for an Entra access token for Key Vault."""

    tenant = urllib.parse.quote(tenant_id, safe="")
    token_url = f"https://login.microsoftonline.com/{tenant}/oauth2/v2.0/token"
    body = urllib.parse.urlencode(
        {
            "client_id": client_id,
            "scope": "https://vault.azure.net/.default",
            # Entra treats the GitHub OIDC JWT as a client assertion for workload identity federation.
            "grant_type": "client_credentials",
            "client_assertion_type": "urn:ietf:params:oauth:client-assertion-type:jwt-bearer",
            "client_assertion": oidc_token,
        }
    ).encode("utf-8")

    req = urllib.request.Request(url=token_url, data=body, method="POST")
    req.add_header("Content-Type", "application/x-www-form-urlencoded")
    try:
        with urllib.request.urlopen(req) as resp:
            token_response = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as err:
        detail = err.read().decode("utf-8", errors="replace")
        fail(f"Failed to exchange OIDC token for Key Vault token: HTTP {err.code}\n{detail}")
    except urllib.error.URLError as err:
        fail(f"Failed to exchange OIDC token for Key Vault token: {err.reason}")
    except json.JSONDecodeError:
        fail("Entra token endpoint response was not valid JSON.")

    access_token = token_response.get("access_token")
    if not isinstance(access_token, str) or not access_token.strip():
        fail("Entra token endpoint response did not include `access_token`.")
    return access_token.strip()


def run_keyvault_sign(
    vault_name: str, key_name: str, key_version: str, digest_b64url: str, access_token: str
) -> str:
    """Sign a SHA-256 digest with a Key Vault key and return encoded signature."""

    encoded_key_name = urllib.parse.quote(key_name, safe="")
    sign_path = f"/keys/{encoded_key_name}/sign"
    # Include key version when provided so callers can pin exact key material.
    if key_version:
        encoded_key_version = urllib.parse.quote(key_version, safe="")
        sign_path = f"/keys/{encoded_key_name}/{encoded_key_version}/sign"
    sign_url = f"https://{vault_name}.vault.azure.net{sign_path}?api-version=7.4"

    # Key Vault sign expects the SHA-256 digest in base64url form.
    sign_body = json.dumps({"alg": "RS256", "value": digest_b64url}, separators=(",", ":")).encode("utf-8")
    req = urllib.request.Request(url=sign_url, data=sign_body, method="POST")
    req.add_header("Authorization", f"Bearer {access_token}")
    req.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(req) as resp:
            sign_result = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as err:
        detail = err.read().decode("utf-8", errors="replace")
        fail(f"Azure Key Vault signing failed: HTTP {err.code}\n{detail}")
    except urllib.error.URLError as err:
        fail(f"Azure Key Vault signing failed: {err.reason}")
    except json.JSONDecodeError:
        fail(
            "Azure Key Vault sign response was not valid JSON."
        )

    # Accept common signature fields to be resilient across SDK/API response shapes.
    signature = sign_result.get("signature") or sign_result.get("value") or sign_result.get("result")
    if not isinstance(signature, str) or not signature.strip():
        fail(
            "Azure Key Vault sign response did not include a signature in 'result', 'value', or 'signature'.\n"
            f"response: {json.dumps(sign_result)}"
        )
    return signature.strip()


def github_request(api_url: str, method: str, path: str, jwt: str, body: dict | None = None) -> dict:
    """Send a GitHub API request authenticated with an app JWT."""

    url = urllib.parse.urljoin(api_url.rstrip("/") + "/", path.lstrip("/"))
    data = None if body is None else json.dumps(body).encode("utf-8")
    req = urllib.request.Request(url=url, data=data, method=method)
    req.add_header("Authorization", f"Bearer {jwt}")
    req.add_header("Accept", "application/vnd.github+json")
    req.add_header("X-GitHub-Api-Version", "2022-11-28")
    if data is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(req) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as err:
        detail = err.read().decode("utf-8", errors="replace")
        raise GithubHttpError(method, url, err.code, detail) from err


def resolve_installation_id(api_url: str, jwt: str, owner: str) -> int:
    """Resolve installation id from owner input or current repository context."""

    if owner:
        encoded_owner = urllib.parse.quote(owner, safe="")
        try:
            org_installation = github_request(api_url, "GET", f"/orgs/{encoded_owner}/installation", jwt)
            return int(org_installation["id"])
        except GithubHttpError as err:
            if err.status != 404:
                fail(str(err))
        user_installation = github_request(api_url, "GET", f"/users/{encoded_owner}/installation", jwt)
        return int(user_installation["id"])

    repository = os.environ.get("GITHUB_REPOSITORY", "")
    if "/" not in repository:
        fail("GITHUB_REPOSITORY is missing or invalid, and no owner input was provided.")
    repo_owner, repo_name = repository.split("/", 1)
    encoded_owner = urllib.parse.quote(repo_owner, safe="")
    encoded_repo = urllib.parse.quote(repo_name, safe="")
    repo_installation = github_request(api_url, "GET", f"/repos/{encoded_owner}/{encoded_repo}/installation", jwt)
    return int(repo_installation["id"])


def write_output(name: str, value: str) -> None:
    """Append a step output value to GITHUB_OUTPUT."""

    output_path = os.environ.get("GITHUB_OUTPUT")
    if not output_path:
        fail("GITHUB_OUTPUT is not set.")
    with open(output_path, "a", encoding="utf-8") as file:
        file.write(f"{name}={value}\n")


def build_app_jwt(
    app_id: str,
    vault_name: str,
    key_name: str,
    key_version: str,
    azure_client_id: str,
    azure_tenant_id: str,
    azure_oidc_audience: str,
    expiration_seconds: int,
) -> str:
    """Build and sign a GitHub App JWT using Azure Key Vault."""

    # Backdate iat slightly to tolerate minor clock skew between systems.
    iat = int(time.time()) - 60
    exp = iat + expiration_seconds
    jwt_header = {"alg": "RS256", "typ": "JWT"}
    jwt_payload = {"iat": iat, "exp": exp, "iss": app_id}

    encoded_header = b64url_encode(json.dumps(jwt_header, separators=(",", ":")).encode("utf-8"))
    encoded_payload = b64url_encode(json.dumps(jwt_payload, separators=(",", ":")).encode("utf-8"))
    signing_input = f"{encoded_header}.{encoded_payload}".encode("utf-8")

    # For RS256, Key Vault signs the SHA-256 digest of the JWS signing input.
    digest_b64url = b64url_encode(hashlib.sha256(signing_input).digest())
    oidc_token = get_actions_oidc_token(azure_oidc_audience)
    keyvault_token = exchange_oidc_for_keyvault_token(azure_tenant_id, azure_client_id, oidc_token)
    signature_from_az = run_keyvault_sign(vault_name, key_name, key_version, digest_b64url, keyvault_token)
    # Normalize the returned signature to canonical base64url for the JWT segment.
    signature_bytes = b64url_decode(signature_from_az)
    if not signature_bytes:
        fail("Azure Key Vault returned an empty signature.")
    signature_b64url = b64url_encode(signature_bytes)

    return f"{encoded_header}.{encoded_payload}.{signature_b64url}"


def mint_installation_token(
    api_url: str,
    app_jwt: str,
    owner: str,
    repositories_raw: str,
) -> tuple[str, int]:
    """Resolve installation id and mint an installation access token."""

    try:
        installation_id = resolve_installation_id(api_url, app_jwt, owner)
    except GithubHttpError as err:
        fail(str(err))

    token_payload: dict = {}
    repositories = parse_repositories(repositories_raw)
    if repositories:
        token_payload["repositories"] = repositories

    try:
        token_response = github_request(
            api_url,
            "POST",
            f"/app/installations/{installation_id}/access_tokens",
            app_jwt,
            token_payload,
        )
    except GithubHttpError as err:
        fail(str(err))

    token = token_response.get("token")
    if not token:
        fail("GitHub API response did not include a token.")
    return token, installation_id


def main() -> None:
    """Read inputs, mint token, and publish action outputs."""

    app_id = read_required_env("INPUT_APP_ID", "app-id")
    vault_name = read_required_env("INPUT_KEY_VAULT_NAME", "key-vault-name")
    key_name = read_required_env("INPUT_KEY_NAME", "key-name")
    key_version = os.environ.get("INPUT_KEY_VERSION", "").strip()
    azure_client_id = read_required_env("INPUT_AZURE_CLIENT_ID", "azure-client-id")
    azure_tenant_id = read_required_env("INPUT_AZURE_TENANT_ID", "azure-tenant-id")
    azure_oidc_audience = os.environ.get("INPUT_AZURE_OIDC_AUDIENCE", "api://AzureADTokenExchange").strip()
    owner = os.environ.get("INPUT_OWNER", "").strip()
    repositories_raw = os.environ.get("INPUT_REPOSITORIES", "")
    api_url = os.environ.get("INPUT_GITHUB_API_URL", "https://api.github.com").strip()
    expiration_seconds = parse_expiration_seconds(os.environ.get("INPUT_JWT_EXPIRATION_SECONDS", "540").strip())

    app_jwt = build_app_jwt(
        app_id,
        vault_name,
        key_name,
        key_version,
        azure_client_id,
        azure_tenant_id,
        azure_oidc_audience,
        expiration_seconds,
    )
    token, installation_id = mint_installation_token(api_url, app_jwt, owner, repositories_raw)

    print(f"::add-mask::{token}")   # Tell GitHub to mask this secret
    write_output("token", token)
    write_output("installation-id", str(installation_id))


if __name__ == "__main__":
    main()
