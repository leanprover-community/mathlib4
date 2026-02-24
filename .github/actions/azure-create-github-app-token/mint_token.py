#!/usr/bin/env python3
"""Mint a GitHub App installation token using Azure Key Vault signing.

This script is invoked by the local composite action. It builds a JWT for a
GitHub App, signs the JWT digest with an Azure Key Vault key, and exchanges the
JWT for an installation access token.
"""

import base64
import hashlib
import json
import os
import subprocess
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
        self.detail = detail


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


def run_az_key_sign(vault_name: str, key_name: str, key_version: str, digest_b64: str) -> str:
    """Sign a SHA-256 digest with a Key Vault key and return encoded signature."""

    cmd = [
        "az",
        "keyvault",
        "key",
        "sign",
        "--vault-name",
        vault_name,
        "--name",
        key_name,
        "--algorithm",
        "RS256",
        "--digest",
        digest_b64,
        "-o",
        "json",
    ]
    if key_version:
        cmd.extend(["--version", key_version])
    proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        fail(
            "Azure Key Vault signing failed.\n"
            f"Command: {' '.join(cmd)}\n"
            f"stdout: {proc.stdout.strip()}\n"
            f"stderr: {proc.stderr.strip()}"
        )
    try:
        sign_result = json.loads(proc.stdout)
    except json.JSONDecodeError:
        fail(
            "Azure Key Vault sign response was not valid JSON.\n"
            f"stdout: {proc.stdout.strip()}\n"
            f"stderr: {proc.stderr.strip()}"
        )

    signature = sign_result.get("result") or sign_result.get("value")
    if not isinstance(signature, str) or not signature.strip():
        fail(
            "Azure Key Vault sign response did not include a signature in 'result' or 'value'.\n"
            f"stdout: {proc.stdout.strip()}"
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


def fail_with_jwt_decode_guidance(err: GithubHttpError, app_id: str, vault_name: str, key_name: str, key_version: str) -> None:
    """Provide actionable hints when GitHub rejects the app JWT."""

    if err.status == 401 and "could not be decoded" in err.detail.lower():
        version_text = key_version if key_version else "<latest>"
        fail(
            f"{err}\n\n"
            "GitHub rejected the app JWT. Common causes:\n"
            "1) app-id does not match the GitHub App that owns this key.\n"
            "2) Key Vault key/version is not the GitHub App private key currently registered in GitHub.\n"
            "3) The selected key version is wrong (or omitted and latest is not the expected version).\n"
            "4) The Key Vault key is not RSA or does not represent the imported GitHub App PEM key.\n\n"
            f"Current inputs: app-id={app_id}, vault={vault_name}, key={key_name}, key-version={version_text}"
        )
    fail(str(err))


def main() -> None:
    """Read inputs, mint token, and publish action outputs."""

    app_id = os.environ.get("INPUT_APP_ID", "").strip()
    vault_name = os.environ.get("INPUT_KEY_VAULT_NAME", "").strip()
    key_name = os.environ.get("INPUT_KEY_NAME", "").strip()
    key_version = os.environ.get("INPUT_KEY_VERSION", "").strip()
    owner = os.environ.get("INPUT_OWNER", "").strip()
    repositories_raw = os.environ.get("INPUT_REPOSITORIES", "")
    api_url = os.environ.get("INPUT_GITHUB_API_URL", "https://api.github.com").strip()
    expiration_raw = os.environ.get("INPUT_JWT_EXPIRATION_SECONDS", "540").strip()

    if not app_id:
        fail("app-id is required.")
    if not vault_name:
        fail("key-vault-name is required.")
    if not key_name:
        fail("key-name is required.")

    try:
        expiration_seconds = int(expiration_raw)
    except ValueError:
        fail(f"jwt-expiration-seconds must be an integer, got: {expiration_raw}")
    if expiration_seconds <= 0 or expiration_seconds > 600:
        fail("jwt-expiration-seconds must be between 1 and 600.")

    iat = int(time.time()) - 60
    exp = iat + expiration_seconds
    jwt_header = {"alg": "RS256", "typ": "JWT"}
    jwt_payload = {"iat": iat, "exp": exp, "iss": app_id}

    encoded_header = b64url_encode(json.dumps(jwt_header, separators=(",", ":")).encode("utf-8"))
    encoded_payload = b64url_encode(json.dumps(jwt_payload, separators=(",", ":")).encode("utf-8"))
    signing_input = f"{encoded_header}.{encoded_payload}".encode("utf-8")

    digest_b64 = base64.b64encode(hashlib.sha256(signing_input).digest()).decode("ascii")
    signature_from_az = run_az_key_sign(vault_name, key_name, key_version, digest_b64)
    signature_bytes = b64url_decode(signature_from_az)
    if not signature_bytes:
        fail("Azure Key Vault returned an empty signature.")
    signature_b64url = b64url_encode(signature_bytes)

    app_jwt = f"{encoded_header}.{encoded_payload}.{signature_b64url}"
    try:
        installation_id = resolve_installation_id(api_url, app_jwt, owner)
    except GithubHttpError as err:
        fail_with_jwt_decode_guidance(err, app_id, vault_name, key_name, key_version)

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
        fail_with_jwt_decode_guidance(err, app_id, vault_name, key_name, key_version)
    token = token_response.get("token")
    if not token:
        fail("GitHub API response did not include a token.")

    print(f"::add-mask::{token}")   # Tell GitHub to mask this secret
    write_output("token", token)
    write_output("installation-id", str(installation_id))


if __name__ == "__main__":
    main()
