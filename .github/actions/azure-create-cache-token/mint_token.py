#!/usr/bin/env python3
"""Mint an Azure access token for cache uploads using GitHub OIDC.

This script is invoked by the local composite action. It fetches a GitHub
Actions OIDC token and exchanges it with Entra for a scoped Azure access token.
"""

import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request


def fail(message: str) -> None:
    """Print an error and exit with status 1."""

    print(message, file=sys.stderr)
    raise SystemExit(1)


def read_required_env(name: str, label: str) -> str:
    """Read and validate a required action input from the environment."""

    value = os.environ.get(name, "").strip()
    if not value:
        fail(f"{label} is required.")
    return value


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
        fail(f"Failed to fetch GitHub OIDC token: HTTP {err.code}\\n{detail}")
    except urllib.error.URLError as err:
        fail(f"Failed to fetch GitHub OIDC token: {err.reason}")
    except json.JSONDecodeError:
        fail("GitHub OIDC response was not valid JSON.")

    oidc_token = oidc_response.get("value")
    if not isinstance(oidc_token, str) or not oidc_token.strip():
        fail("GitHub OIDC response did not include token in `value`.")
    return oidc_token.strip()


def exchange_oidc_for_access_token(tenant_id: str, client_id: str, oidc_token: str, scope: str) -> str:
    """Exchange a GitHub OIDC token for an Entra access token."""

    tenant = urllib.parse.quote(tenant_id, safe="")
    token_url = f"https://login.microsoftonline.com/{tenant}/oauth2/v2.0/token"
    body = urllib.parse.urlencode(
        {
            "client_id": client_id,
            "scope": scope,
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
        fail(f"Failed to exchange OIDC token for Azure access token: HTTP {err.code}\\n{detail}")
    except urllib.error.URLError as err:
        fail(f"Failed to exchange OIDC token for Azure access token: {err.reason}")
    except json.JSONDecodeError:
        fail("Entra token endpoint response was not valid JSON.")

    access_token = token_response.get("access_token")
    if not isinstance(access_token, str) or not access_token.strip():
        fail("Entra token endpoint response did not include `access_token`.")
    return access_token.strip()


def write_output(name: str, value: str) -> None:
    """Append a step output value to GITHUB_OUTPUT."""

    output_path = os.environ.get("GITHUB_OUTPUT")
    if not output_path:
        fail("GITHUB_OUTPUT is not set.")
    with open(output_path, "a", encoding="utf-8") as file:
        file.write(f"{name}={value}\\n")


def main() -> None:
    """Mint a scoped Azure token and expose it as action output."""

    azure_client_id = read_required_env("INPUT_AZURE_CLIENT_ID", "azure-client-id")
    azure_tenant_id = read_required_env("INPUT_AZURE_TENANT_ID", "azure-tenant-id")
    azure_oidc_audience = os.environ.get("INPUT_AZURE_OIDC_AUDIENCE", "api://AzureADTokenExchange").strip()
    azure_scope = os.environ.get("INPUT_AZURE_SCOPE", "https://storage.azure.com/.default").strip()

    if not azure_oidc_audience:
        fail("azure-oidc-audience must not be empty.")
    if not azure_scope:
        fail("azure-scope must not be empty.")

    oidc_token = get_actions_oidc_token(azure_oidc_audience)
    access_token = exchange_oidc_for_access_token(azure_tenant_id, azure_client_id, oidc_token, azure_scope)
    write_output("token", access_token)


if __name__ == "__main__":
    main()
