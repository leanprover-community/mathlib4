#!/usr/bin/env python3

import os
import requests
from datetime import datetime, timedelta

def get_old_unassigned_prs():
    url = "https://api.github.com/graphql"
    token = os.getenv('GITHUB_TOKEN')  # read token from environment variable
    headers = {"Authorization": f"bearer {token}"}

    print("Making request to GitHub API...")

    response = requests.get(url, headers=headers)
    response.raise_for_status()

    print("Successfully connected to GitHub API...")

    prs = response.json()

    five_days_ago = (datetime.now() - timedelta(days=5)).isoformat()

    query = """
    query {
      repository(owner:"leanprover-community", name:"mathlib4") {
        pullRequests(first:100, states:OPEN, orderBy:{field:CREATED_AT, direction:DESC}) {
          nodes {
            title
            url
            createdAt
            updatedAt
            labels(first:10) {
              nodes {
                name
              }
            }
            assignees(first:1) {
              nodes {
                login
              }
            }
            commits(last:1) {
              nodes {
                commit {
                  status {
                    state
                  }
                }
              }
            }
          }
        }
      }
    }
    """

    response = requests.post(url, headers=headers, json={'query': query})
    response.raise_for_status()

    print("Successfully fetched data from GitHub API...")

    prs = response.json()['data']['repository']['pullRequests']['nodes']

    old_unassigned_prs = []
    for pr in prs:
        print ("Checking PR: ", pr['title'])
        labels = [label['name'] for label in pr['labels']['nodes']]
        if 'awaiting-review' in labels \
            and 'blocked-by-other-PR' not in labels \
            and not pr['assignees']['nodes'] \
            and pr['createdAt'] < five_days_ago:

            commit_status = pr['commits']['nodes'][0]['commit']['status']
            if commit_status is not None and commit_status['state'] == 'SUCCESS':
                old_unassigned_prs.append(pr)

    return old_unassigned_prs

def print_prs(prs):
    for pr in prs:
        print(f"Title: {pr['title']}")
        print(f"URL: {pr['html_url']}")
        print(f"Created at: {pr['created_at']}")
        print(f"Last updated at: {pr['updated_at']}")
        print(f"Labels: {', '.join(label['name'] for label in pr['labels'])}")
        print("--------------------------------------------------")

old_unassigned_prs = get_old_unassigned_prs()
print_prs(old_unassigned_prs)
