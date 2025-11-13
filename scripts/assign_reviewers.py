"""
Download and parse a .json file containing reviewer assignments for pull requests,
and make the github API calls to add these users as assignees.

This script assumes |curl| is installed and on PATH,
and that a github token with `public_repo` permissions is passed in via the
|ASSIGN_REVIEWERS_TOKEN| environment variable.
"""
import json
import os
import sys
import subprocess

ASSIGN_REVIEWERS_TOKEN = os.getenv('ASSIGN_REVIEWERS_TOKEN')
if ASSIGN_REVIEWERS_TOKEN is None:
    print('Please ensure that the ASSIGN_REVIEWERS_TOKEN environment variable is set.')
    sys.exit(1)

# Make the github API call to assign mathlib PR |number| to user |handle|.
# Any existing assignee is kept; specifying a non-existent user does nothing.
# Github's assignment syntax is documented at
# https://docs.github.com/en/rest/issues/assignees?apiVersion=2022-11-28#add-assignees-to-an-issue.
def call(number: int, handle: str) -> bool:
    print(f"assigning PR {number} to {handle}")
    url = f"https://api.github.com/repos/leanprover-community/mathlib4/issues/{number}/assignees"
    arguments_DO_NOT_PRINT = [
        "--fail-with-body", "--location", "--request", "POST",
        '--header', 'Accept: application/vnd.github+json',
        '--header', f'Authorization: Bearer {ASSIGN_REVIEWERS_TOKEN}',
        '--header', "X-GitHub-Api-Version: 2022-11-28",
        url, '--data', f'{{"assignees":["{handle}"]}}'
    ]
    out = subprocess.run(["curl"] + arguments_DO_NOT_PRINT, capture_output=True, encoding="utf-8")
    if out.stdout:
        print("output from calling CURL:\n" + out.stdout)
    if out.stderr:
        print("standard error output is:\n" + out.stderr)
    if out.returncode != 0:
        print(f"error: curl failed to assign reviewer {handle} to PR {number}")
        return False
    return True

if __name__ == '__main__':
    # Download the assignments file using curl.
    url = "https://leanprover-community.github.io/queueboard/automatic_assignments.json"
    args = ["curl", "--output", "assignments.json", url]
    print("trace: about to download the assignments file using curl...")
    out = subprocess.run(args, capture_output=True, encoding="utf-8")
    if out.stdout:
        print("standard output is: \n" + out.stdout)
    if out.stderr:
        print("standard error is: \n" + out.stderr)
    if out.returncode != 0:
        print(f"error: curl failed to download the assignment file at {url}"
            "Please make sure curl is installed and on your PATH.")
        sys.exit(1)

    with open('assignments.json', 'r') as fi:
        data = json.load(fi)
    all_api_calls_succeeded = True
    for (number, user_handle) in data.items():
        # If the number of API calls is greater than 2000 per hour, put a wait in here.
        # The limit is 5000/hr per https://docs.github.com/en/rest/using-the-rest-api/rate-limits-for-the-rest-api?apiVersion=2022-11-28#primary-rate-limit-for-authenticated-users
        all_api_calls_succeeded = call(number, user_handle) and all_api_calls_succeeded
    if not all_api_calls_succeeded:
        print("Some API calls were not successful")
        sys.exit(1)
