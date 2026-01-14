#!/usr/bin/env python3

import argparse
import json
import platform
import re
import shlex
import subprocess
import sys
from typing import NoReturn


def http_url(repo: str) -> str:
    return f"https://github.com/{repo}.git"


def ssh_url(repo: str) -> str:
    return f"git@github.com:{repo}.git"


def from_url(url: str) -> str | None:
    regex = r"(?:https://github\.com/|git@github\.com/)(.*)\.git"
    if match := re.fullmatch(regex, url):
        return match.group(1)


UPSTREAM: str = "upstream"
ORIGIN: str = "origin"

MATHLIB_REPO: str = "leanprover-community/mathlib4"
MATHLIB_HTTP_URL: str = http_url(MATHLIB_REPO)
MATHLIB_SSH_URL: str = ssh_url(MATHLIB_REPO)
MATHLIB_URLS: set[str] = {MATHLIB_HTTP_URL, MATHLIB_SSH_URL}

GRAY = "\033[37m"
RED = "\033[91m"
GREEN = "\033[92m"
YELLOW = "\033[93m"
BLUE = "\033[94m"
BOLD = "\033[1m"
END = "\033[0m"

if platform.system() == "Windows":
    # Windows doesn't support ANSI colors by default, so we'll use empty strings
    GRAY = ""
    RED = ""
    GREEN = ""
    YELLOW = ""
    BLUE = ""
    BOLD = ""
    END = ""


def print_step(i: int, msg: str) -> None:
    print(f"{BOLD}{BLUE}Step {i}:{END} {msg}")


def print_info(msg: str) -> None:
    print(f"{BOLD}{GREEN}INFO:{END} {msg}")


def print_warn(msg: str) -> None:
    print(f"{BOLD}{YELLOW}WARNING:{END} {msg}")


def print_error(msg: str) -> None:
    print(f"{BOLD}{RED}ERROR:{END} {msg}")


def abort(msg: str, code: int = 1) -> NoReturn:
    print_error(msg)
    sys.exit(code)


def run_cmd(*cmd: str) -> None:
    try:
        print(f"{GRAY}$ {shlex.join(cmd)}{END}")
        subprocess.check_call(cmd)
    except subprocess.CalledProcessError as e:
        abort(f"Command failed with status {e.returncode}")


def run_stdout(*cmd: str, fatal: bool = True) -> str:
    try:
        return subprocess.check_output(
            cmd,
            text=True,
            encoding="utf8",
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError as e:
        if fatal:
            abort(f"Command failed with status {e.returncode}: {shlex.join(cmd)}")
        raise e


def run_check(*cmd: str) -> None:
    subprocess.check_call(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def ask_yes_no(prompt: str) -> bool:
    while True:
        response = input(f"{prompt} [Y/n]: ").strip()
        if response.lower() in {"y", "yes"}:
            return True
        if response.lower() in {"n", "no"}:
            return False
        if not response:
            return True
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
        abort(f"The program {program!r} is not installed correctly.")


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


def git_rename_remote(remote: str, to: str) -> None:
    run_cmd("git", "remote", "rename", "--", remote, to)


def git_fetch_all() -> None:
    run_cmd("git", "fetch", "--all", "--prune")


def git_get_branch_remote(branch: str) -> str | None:
    # `git config get` was only added in git 2.46.0
    try:
        out = run_stdout(
            "git",
            "config",
            f"branch.{branch}.remote",
            fatal=False,
        )
        return out.removesuffix("\n")
    except subprocess.CalledProcessError:
        pass


def git_get_branch_push_remote(branch: str) -> str | None:
    # `git config get` was only added in git 2.46.0
    try:
        out = run_stdout(
            "git",
            "config",
            f"branch.{branch}.pushRemote",
            fatal=False,
        )
        return out.removesuffix("\n")
    except subprocess.CalledProcessError:
        pass


def git_set_branch_remote(branch: str, remote: str) -> str | None:
    run_cmd("git", "branch", f"--set-upstream-to={remote}/master", "--", branch)


def git_set_branch_push_remote(branch: str, remote: str) -> str | None:
    # `git config set` was only added in git 2.46.0
    run_cmd("git", "config", "--", f"branch.{branch}.pushRemote", remote)


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
        abort(f"The program {program!r} is not installed correctly.")


def gh_ensure_logged_in() -> None:
    try:
        run_check("gh", "auth", "status")
    except subprocess.CalledProcessError:
        abort("You must be logged in with 'gh'. Run `gh auth login`.")


def gh_get_default_repo() -> str:
    return run_stdout("gh", "repo", "set-default", "--view").strip()


def gh_set_default_repo(repo: str) -> None:
    run_cmd("gh", "repo", "set-default", "--", repo)


def gh_get_username() -> str:
    [username] = run_stdout("gh", "api", "user", "-q", ".login").splitlines()
    return username


def gh_get_repo_parent(repo: str) -> str | None:
    try:
        [parent] = run_stdout(
            "gh", "api", f"repos/{repo}", "-q", ".parent.full_name"
        ).splitlines()
        return parent
    except subprocess.CalledProcessError:
        return None


def gh_get_all_forks() -> dict[str, str]:
    graphql_query = """
    query($endCursor: String) {
      repositoryOwner(login: "Garmelon") {
        repositories(first: 10, after: $endCursor, isFork: true) {
          nodes {
            nameWithOwner
            parent { nameWithOwner }
          }
          pageInfo { hasNextPage, endCursor }
        }
      }
    }
    """

    jq_query = """
    .data.repositoryOwner.repositories.nodes[] |
    { parent: .parent.nameWithOwner, fork: .nameWithOwner }
    """

    out_str = run_stdout(
        "gh",
        "api",
        "graphql",
        "--paginate",
        "-f",
        f"query={graphql_query}",
        "-q",
        jq_query,
    )

    result: dict[str, str] = {}
    for line in out_str.splitlines():
        repo = json.loads(line)
        result[repo["fork"]] = repo["parent"]

    return result


def gh_find_mathlib_fork(username: str, origin_url: str | None) -> str | None:
    if origin_url is not None:
        origin = from_url(origin_url)
        if origin is not None:
            parent = gh_get_repo_parent(origin)
            if parent == MATHLIB_REPO:
                return origin

    guess = f"{username}/mathlib4"
    parent = gh_get_repo_parent(guess)
    if parent == MATHLIB_REPO:
        return guess

    forks = gh_get_all_forks()
    for fork, parent in forks.items():
        if parent == MATHLIB_REPO:
            return fork


def gh_fork() -> None:
    run_cmd("gh", "repo", "fork", "--default-branch-only", "--remote")


##################
## Command: fix ##
##################


def cmd_fix_update_remote(
    remote: str,
    target: str,
    target_url: str,
    allowed_urls: set[str],
) -> None:
    allowed_urls = allowed_urls | {target_url}
    remotes = git_get_remotes()

    url = remotes.get(remote)
    if url in allowed_urls:
        return

    # Delete remote if it points to the wrong place.
    if url is not None:
        print_warn(f"Remote {remote!r} does not point to {target}.")
        if not ask_yes_no(f"Delete and replace remote {remote!r}?"):
            abort(f"Remote {remote!r} must point to {target}.")
        git_remove_remote(remote)
        remotes = git_get_remotes()

    # Try to find and rename a remote that already points to the correct place.
    for name, url in remotes.items():
        if url in allowed_urls:
            print_info(f"Remote {name!r} points to {target}.")
            if ask_yes_no(f"Rename remote {name!r} to {remote!r}?"):
                git_rename_remote(name, remote)
                remotes = git_get_remotes()
                break

    # Create remote if it doesn't exist by now.
    if remote not in remotes:
        print_warn(f"Remote {remote!r} does not exist.")
        if not ask_yes_no(f"Create remote {remote!r}?"):
            abort(f"Remote {remote!r} must point to {target}.")
        git_add_remote(remote, target_url)


def cmd_fix_update_default_gh_repo() -> None:
    repo = gh_get_default_repo()
    if repo == MATHLIB_REPO:
        return

    print_warn("The gh default repo does not point to mathlib.")
    print("See `gh repo set-default --help` for more info.")
    if not ask_yes_no("Update gh default repo?"):
        abort("The gh default repo must point to mathlib.")

    gh_set_default_repo(MATHLIB_REPO)


def cmd_fix_set_origin_to_fork(fork: str) -> None:
    pass


def cmd_fix_create_new_fork() -> None:
    remotes = git_get_remotes()
    if ORIGIN in remotes:
        print_warn(f"Remote {ORIGIN!r} is in the way of the fork.")
        if not ask_yes_no(f"Remove remote {ORIGIN!r}?"):
            abort(f"Remote {ORIGIN!r} must be removed before the fork is created.")
        git_remove_remote(ORIGIN)

    if not ask_yes_no("Create new mathlib fork?"):
        abort("Please fork mathlib yourself and re-run this script.")
    gh_fork()


def cmd_fix_update_origin_to_fork(fork: str) -> None:
    fork_ssh = ssh_url(fork)
    fork_http = http_url(fork)
    fork_urls = {fork_ssh, fork_http}
    cmd_fix_update_remote(ORIGIN, "your fork of mathlib", fork_ssh, fork_urls)


def cmd_fix_update_master_remotes() -> None:
    branch = "master"

    remote = git_get_branch_remote(branch)
    if remote != UPSTREAM:
        print_warn(f"Branch {branch!r} should have remote {UPSTREAM!r}.")
        if not ask_yes_no(f"Update remote of {branch!r}?"):
            return
        git_set_branch_remote(branch, UPSTREAM)

    push_remote = git_get_branch_push_remote("master")
    if push_remote != ORIGIN:
        print_warn(f"Branch {branch!r} should have pushRemote {ORIGIN!r}.")
        if not ask_yes_no(f"Update pushRemote of {branch!r}?"):
            return
        git_set_branch_push_remote(branch, ORIGIN)


def cmd_fix() -> None:
    git_ensure_installed()
    git_ensure_in_repo()
    gh_ensure_installed()
    gh_ensure_logged_in()
    username = gh_get_username()

    print_step(1, f"Remote {UPSTREAM!r} should point to mathlib.")
    cmd_fix_update_remote(UPSTREAM, "mathlib", MATHLIB_HTTP_URL, MATHLIB_URLS)

    print_step(2, "Default gh repo should point to mathlib.")
    cmd_fix_update_default_gh_repo()

    print_step(3, f"Remote {ORIGIN!r} should point to your fork of mathlib.")
    remotes = git_get_remotes()
    fork = gh_find_mathlib_fork(username, remotes.get(ORIGIN))
    if fork is None:
        print_info("Found no mathlib fork.")
        cmd_fix_create_new_fork()
    else:
        print_info(f"Found a mathlib fork at {fork}.")
        cmd_fix_update_origin_to_fork(fork)

    print_step(4, "Updating remotes...")
    git_fetch_all()

    print_step(5, "Check remotes of branch 'master'.")
    cmd_fix_update_master_remotes()


##########
## Main ##
##########


def main() -> None:
    parser = argparse.ArgumentParser()
    # TODO --origin-https option?
    # TODO --upstream-ssh option?

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
