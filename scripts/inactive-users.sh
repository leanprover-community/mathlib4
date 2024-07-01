#!/bin/bash

# Install the required Python package if not already installed
pip3 show requests &> /dev/null
if [ $? -ne 0 ]; then
    echo "Installing required Python package 'requests'..."
    pip3 install requests
fi

# Python script
python3 - << 'END_PYTHON'
import requests
import json
import subprocess
from datetime import datetime, timedelta

# Function to get GitHub token using `gh` CLI
def get_github_token():
    result = subprocess.run(['gh', 'auth', 'token'], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if result.returncode != 0:
        raise Exception(f"Failed to get GitHub token: {result.stderr}")
    return result.stdout.strip()

# Function to make a GraphQL query to GitHub API
def github_graphql_query(query, variables=None):
    url = "https://api.github.com/graphql"
    headers = {
        "Authorization": f"Bearer {TOKEN}",
        "Content-Type": "application/json"
    }
    payload = {"query": query}
    if variables:
        payload["variables"] = variables
    response = requests.post(url, headers=headers, json=payload)
    response.raise_for_status()
    return response.json()

# Set variables
REPO_OWNER = "leanprover-community"
REPO_NAME = "mathlib4"
MONTHS_AGO = 12

# Calculate the date X months ago
start_date = (datetime.now() - timedelta(days=30 * MONTHS_AGO)).strftime('%Y-%m-%dT%H:%M:%SZ')

# Get the GitHub token
TOKEN = get_github_token()

# GraphQL query to get repository collaborators with pagination
collaborators_query = """
query($owner: String!, $name: String!, $cursor: String) {
  repository(owner: $owner, name: $name) {
    collaborators(first: 100, after: $cursor) {
      pageInfo {
        endCursor
        hasNextPage
      }
      edges {
        node {
          login
        }
      }
    }
  }
}
"""

# Fetch all collaborators with pagination
collaborators = []
cursor = None
while True:
    variables = {"owner": REPO_OWNER, "name": REPO_NAME, "cursor": cursor}
    try:
        data = github_graphql_query(collaborators_query, variables)
    except requests.exceptions.RequestException as e:
        print(f"Error fetching collaborators: {e}")
        break
    if 'data' not in data:
        print(f"Unexpected response structure: {data}")
        break
    collaborators.extend(edge['node']['login'] for edge in data['data']['repository']['collaborators']['edges'])
    page_info = data['data']['repository']['collaborators']['pageInfo']
    if not page_info['hasNextPage']:
        break
    cursor = page_info['endCursor']

# Check commit history for each collaborator using REST API
inactive_users = []
headers = {
    "Authorization": f"Bearer {TOKEN}"
}
for user in collaborators:
    url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/commits?author={user}&since={start_date}"
    try:
        response = requests.get(url, headers=headers)
        response.raise_for_status()
        commits = response.json()
        if not commits:
            inactive_users.append(user)
    except requests.exceptions.RequestException as e:
        print(f"Error fetching commit history for {user}: {e}")
        continue

# Output the list of inactive users
print(f"Users with write access who have not pushed a commit in the last {MONTHS_AGO} months:")
for user in inactive_users:
    print(user)
END_PYTHON
