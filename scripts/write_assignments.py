"""
Read a file |assignments.json| containing reviewer assignments for pull requests,
parse its contents and generate a shell script making the github API calls to add these users
as assignees.
"""
import json

# Create the github API call to assign mathlib PR |number| to user |handle|.
# Any existing assignee is kept; specifying a non-existent user does nothing.
# Github's assignment syntax is documented at
# https://docs.github.com/en/rest/issues/assignees?apiVersion=2022-11-28#add-assignees-to-an-issue.
def call(number: int, handle: str) -> str:
    raw = f'''curl --location --request POST --header "Accept: application/vnd.github+json" \\
        --header "authorization: Bearer ${{ secrets.ASSIGN_REVIEWERS }}" \\
        --header "X-GitHub-Api-Version: 2022-11-28" \\
        https://api.github.com/repos/leanprover-community/mathlib4/issues/{number}/assignees \\
        --data \'{{"assignees":["{handle}"]}}\''''
    return raw.replace("        ", "  ")

if __name__ == '__main__':
    with open('assignments.json', 'r') as fi:
        data = json.load(fi)
    output = [call(number, user_handle) for (number, user_handle) in data.items()]
    with open('assign_users.sh', 'w') as outfile:
        for (number, user_handle) in data.items():
            print(f"assigning PR {number} to {user_handle}")
        outfile.write("\n".join(output) + '\n')
