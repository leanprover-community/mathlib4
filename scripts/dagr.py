#!/usr/bin/env python3

import os
import requests
from collections import defaultdict
import time
from datetime import datetime, timedelta

# Plan
#
# Histogram of maintainer activity (last 4 weeks, number of actions per week, comments etc)
# Add a column with how many PRs are assigned to each maintainer
# Add a column with average maintainer response time
# Another dashboard with reviewer stats, that maintainers can use to request reviews

def get_team_members():
    url = "https://api.github.com/graphql"
    token = os.getenv('GITHUB_TOKEN')  # read token from environment variable
    headers = {"Authorization": f"bearer {token}"}

    query = """
    query {
      organization(login: "leanprover-community") {
        team(slug: "mathlib-maintainers") {
          members {
            nodes {
              login
            }
          }
        }
      }
    }
    """

    response = requests.post(url, headers=headers, json={'query': query})
    response.raise_for_status()

    data = response.json()['data']
    team_members = [node['login'] for node in data['organization']['team']['members']['nodes']]

    return team_members

def get_team_activity(team_members, endCursorIssues=None, endCursorPRs=None):
    url = "https://api.github.com/graphql"
    token = os.getenv('GITHUB_TOKEN')  # token from
    headers = {"Authorization": f"bearer {token}"}

    query = """
    query($endCursorIssues: String, $endCursorPRs: String) {
      rateLimit {
        limit
        cost
        remaining
        resetAt
      }
      repository(owner:"leanprover-community", name:"mathlib4") {
        issues(first:100, after:$endCursorIssues, orderBy:{field:UPDATED_AT, direction:DESC}) {
          pageInfo {
            endCursor
            hasNextPage
          }
          nodes {
            title
            url
            updatedAt
            comments(last:100) {
              nodes {
                author {
                  login
                }
                createdAt
                body
              }
            }
            timelineItems(last:100) {
              nodes {
                ... on IssueComment {
                  author {
                    login
                  }
                  createdAt
                  body
                }
                ... on ClosedEvent {
                  actor {
                    login
                  }
                  createdAt
                }
              }
            }
          }
        }
        pullRequests(first:100, after:$endCursorPRs, orderBy:{field:UPDATED_AT, direction:DESC}) {
          pageInfo {
            endCursor
            hasNextPage
          }
          nodes {
            title
            url
            updatedAt
            comments(last:100) {
              nodes {
                author {
                  login
                }
                createdAt
                body
              }
            }
            timelineItems(last:100) {
              nodes {
                ... on IssueComment {
                  author {
                    login
                  }
                  createdAt
                  body
                }
                ... on ClosedEvent {
                  actor {
                    login
                  }
                  createdAt
                }
              }
            }
          }
        }
      }
    }
    """

    variables = {
        "endCursorIssues": endCursorIssues,
        "endCursorPRs": endCursorPRs
    }

    for _ in range(3):
        try:
            response = requests.post(url, headers=headers, json={'query': query, 'variables': variables})
            response.raise_for_status()
            break
        except requests.exceptions.HTTPError as e:
            print(f"Request failed with error {e}. Retrying...")
            time.sleep(5)
    else:
        print("Failed to get data after 3 attempts. Exiting.")
        return activity

    data = response.json()['data']
    rate_limit = data['rateLimit']

    print(f"Rate limit remaining: {rate_limit['remaining']}")
    print(f"Rate limit reset at: {datetime.fromisoformat(rate_limit['resetAt'].replace('Z', ''))}")

    pageInfoIssues = data['repository']['issues']['pageInfo']
    pageInfoPRs = data['repository']['pullRequests']['pageInfo']
    nodesIssues = data['repository']['issues']['nodes']
    nodesPRs = data['repository']['pullRequests']['nodes']

    activity = []
    for node in nodesIssues + nodesPRs:
        if 'author' in node and node['author'] and 'login' in node['author']:
            if node['author']['login'] in team_members:
                activity.append(node)

    if pageInfoIssues['hasNextPage'] and pageInfoPRs['hasNextPage']:
        activity += get_team_activity(team_members, pageInfoIssues['endCursor'], pageInfoPRs['endCursor'])
    elif pageInfoIssues['hasNextPage']:
        activity += get_team_activity(team_members, pageInfoIssues['endCursor'], endCursorPRs)
    elif pageInfoPRs['hasNextPage']:
        activity += get_team_activity(team_members, endCursorIssues, pageInfoPRs['endCursor'])

    return activity

def print_activity(activity):
    activity_by_user = defaultdict(set)

    for item in activity:
        date = datetime.strptime(item['createdAt'], '%Y-%m-%dT%H:%M:%SZ').date()
        activity_by_user[item['author']['login']].add(date)

    four_weeks_ago = (datetime.now() - timedelta(weeks=4)).date()

    for user, dates in activity_by_user.items():
        user = (user[:8]) if len(user) > 8 else user.ljust(8)
        activity_string = ''
        for i in range(28):
            date = four_weeks_ago + timedelta(days=i)
            activity_string += 'x' if date in dates else '-'
        print(f'{user}: {activity_string}')


team_members = get_team_members()
activity = get_team_activity(team_members)

print(len(activity))
print("=====================================")

print_activity(activity)



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

# old_unassigned_prs = get_old_unassigned_prs()
# print_prs(old_unassigned_prs)
