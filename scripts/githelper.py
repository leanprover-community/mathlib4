#!/usr/bin/env python3

import argparse
import shlex
import subprocess
import sys
from typing import NoReturn

UPSTREAM: str = "upstream"
ORIGIN: str = "origin"

MATHLIB_REPO: str = "leanprover-community/mathlib4"
MATHLIB_HTTP_URL: str = f"https://github.com/{MATHLIB_REPO}.git"
MATHLIB_SSH_URL: str = f"git@github.com:{MATHLIB_REPO}.git"
MATHLIB_URLS: set[str] = {MATHLIB_HTTP_URL, MATHLIB_SSH_URL}

GREEN = "\033[92m"
YELLOW = "\033[93m"
RED = "\033[91m"
BLUE = "\033[94m"
BOLD = "\033[1m"
END = "\033[0m"


def print_warn(msg: str) -> None:
    print(f"{BOLD}{YELLOW}WARNING:{END} {msg}")


def print_error(msg: str) -> None:
    print(f"{BOLD}{RED}ERROR:{END} {msg}")


def abort(msg: str, code: int = 1) -> NoReturn:
    print_error(msg)
    sys.exit(code)


def run_cmd(*cmd: str) -> None:
    try:
        subprocess.check_call(cmd)
    except subprocess.CalledProcessError as e:
        abort(f"Command failed with status {e.returncode}: {shlex.join(cmd)}")


def run_stdout(*cmd: str) -> str:
    try:
        return subprocess.check_output(
            cmd,
            text=True,
            encoding="utf8",
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError as e:
        abort(f"Command failed with status {e.returncode}: {shlex.join(cmd)}")


def run_check(*cmd: str) -> None:
    subprocess.check_call(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def ask_yes_no(prompt: str) -> bool:
    while True:
        response = input(f"{prompt} [y/n]: ")
        if response.lower() in {"y", "yes"}:
            return True
        if response.lower() in {"n", "no"}:
            return False
        if not response:
            continue
        print("Response not recognized, please answer 'y' or 'n'.")
    return False  # Unreachable


##################
## Git commands ##
##################


def git_ensure_installed() -> None:
    program = "git"
    try:
        run_check(program, "--version")
    except FileNotFoundError:
        abort(f"The program {program!r} is not installed.")
    except subprocess.CalledProcessError:
        abort(f"The program {program!r} is not installed correcty.")


def git_ensure_in_repo() -> None:
    try:
        run_check("git", "status")
    except subprocess.CalledProcessError:
        abort("This script must be executed inside a git repo.")


def git_get_remote_names() -> list[str]:
    remotes = run_stdout("git", "remote").splitlines()
    remotes.sort()
    return remotes


def git_get_remote_url(remote: str) -> str:
    pull_out = run_stdout("git", "remote", "get-url", "--all", "--", remote)
    push_out = run_stdout("git", "remote", "get-url", "--all", "--push", "--", remote)
    pull_lines = pull_out.splitlines()
    push_lines = push_out.splitlines()

    if not pull_lines:
        abort(f"No URL found for remote {remote!r}.")

    if pull_lines != push_lines:
        print_warn(f"Remote {remote!r} pull and push URLs differ, ignoring push URLs.")

    if len(pull_lines) > 1:
        print_warn(f"Remote {remote!r} has more than one URL, ignoring all but first.")

    return pull_lines[0]


def git_get_remotes() -> dict[str, str]:
    return {remote: git_get_remote_url(remote) for remote in git_get_remote_names()}


def git_remove_remote(remote: str) -> None:
    run_cmd("git", "remote", "remove", "--", remote)


def git_add_remote(remote: str, url: str) -> None:
    run_cmd("git", "remote", "add", "--", remote, url)


#################
## Gh commands ##
#################


def gh_ensure_installed() -> None:
    program = "gh"
    try:
        run_check(program, "--version")
    except FileNotFoundError:
        abort(f"The program {program!r} is not installed.")
    except subprocess.CalledProcessError:
        abort(f"The program {program!r} is not installed correcty.")


def gh_ensure_logged_in() -> None:
    # Versions of gh before v2.31.0 print this info on stderr, not stdout.
    # See https://github.com/cli/cli/issues/7447
    try:
        run_check("gh", "auth", "status")
    except subprocess.CalledProcessError:
        abort("You must be logged in with 'gh'. Run `gh auth login`.")


def gh_get_default_repo() -> str:
    return run_stdout("gh", "repo", "set-default", "--view").strip()


def gh_set_default_repo(repo: str) -> None:
    run_cmd("gh", "repo", "set-default", "--", repo)


##################
## Command: fix ##
##################


def cmd_fix_add_missing_upstream() -> None:
    remotes = git_get_remotes()
    if UPSTREAM in remotes:
        return

    print_warn(f"Remote {UPSTREAM!r} does not exist.")
    if not ask_yes_no(f"Create remote {UPSTREAM!r}?"):
        abort(f"Remote {UPSTREAM!r} must point to mathlib.")

    git_add_remote(UPSTREAM, MATHLIB_HTTP_URL)


def cmd_fix_replace_wrong_upstream() -> None:
    url = git_get_remotes().get(UPSTREAM)
    if url is None:
        return  # No upstream means no wrong upstream
    if url in MATHLIB_URLS:
        return

    print_warn(f"Remote {UPSTREAM!r} does not point to mathlib.")
    print("Expected it to point to")
    print(f"- {MATHLIB_HTTP_URL}")
    print(f"- {MATHLIB_SSH_URL}")
    print("Instead, it pointed to:")
    print(f"- {url}")
    if not ask_yes_no(f"Delete and replace remote {UPSTREAM!r}?"):
        abort(f"Remote {UPSTREAM!r} must point to mathlib.")

    git_remove_remote(UPSTREAM)
    git_add_remote(UPSTREAM, MATHLIB_HTTP_URL)


def cmd_fix_replace_wrong_default_gh_repo() -> None:
    repo = gh_get_default_repo()
    if repo == MATHLIB_REPO:
        return

    print_warn("The gh default repo does not point to mathlib.")
    print("See `gh repo set-default --help` for more info.")
    if not ask_yes_no("Update gh default repo?"):
        abort("The gh default repo must point to mathlib.")

    gh_set_default_repo(MATHLIB_REPO)


def cmd_fix() -> None:
    git_ensure_installed()
    git_ensure_in_repo()
    cmd_fix_add_missing_upstream()
    cmd_fix_replace_wrong_upstream()

    gh_ensure_installed()
    gh_ensure_logged_in()
    cmd_fix_replace_wrong_default_gh_repo()


##########
## Main ##
##########


def main() -> None:
    parser = argparse.ArgumentParser()

    subparsers = parser.add_subparsers(required=True)

    p_fix = subparsers.add_parser("fix")
    p_fix.set_defaults(subcommand="fix")

    args = parser.parse_args()
    match args.subcommand:
        case "fix":
            cmd_fix()


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print()
        abort("Aborted by user")
