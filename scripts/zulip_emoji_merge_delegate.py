#!/usr/bin/env python3
import sys
import zulip
import requests
import re

# Usage:
# python scripts/zulip_emoji_merge_delegate.py $ZULIP_API_KEY $ZULIP_EMAIL $ZULIP_SITE $GITHUB_TOKEN
# See .github/workflows/zulip_emoji_merge_delegate.yaml for the meaning of these variables

ZULIP_API_KEY = sys.argv[1]
ZULIP_EMAIL = sys.argv[2]
ZULIP_SITE = sys.argv[3]
GITHUB_TOKEN = sys.argv[4]

# Initialize Zulip client
client = zulip.Client(
    email=ZULIP_EMAIL,
    api_key=ZULIP_API_KEY,
    site=ZULIP_SITE
)

# Fetch the last 200 messages
response = client.get_messages({
    "anchor": "newest",
    "num_before": 200,
    "num_after": 0,
    "narrow": [{"operator": "channel", "operand": "PR reviews"}],
})

messages = response['messages']
pr_pattern = re.compile(r'https://github\.com/leanprover-community/mathlib4/pull/(\d+)')

for message in messages:
    content = message['content']
    match = pr_pattern.search(content)
    if match:
        pr_number = match.group(1)
        # Check for emoji reactions
        reactions = message['reactions']
        has_peace_sign = any(reaction['emoji_name'] == 'peace_sign' for reaction in reactions)
        has_bors = any(reaction['emoji_name'] == 'bors' for reaction in reactions)
        has_merge = any(reaction['emoji_name'] == 'merge' for reaction in reactions)

        pr_url = f"https://api.github.com/repos/leanprover-community/mathlib4/pulls/{pr_number}"
        pr_response = requests.get(pr_url, headers={"Authorization": GITHUB_TOKEN})
        pr_data = pr_response.json()
        labels = [label['name'] for label in pr_data['labels']]

        if 'delegated' in labels:
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "peace_sign"
            })
        elif 'ready-to-merge' in labels:
            if has_peace_sign:
                client.remove_reaction({
                    "message_id": message['id'],
                    "emoji_name": "peace_sign"
                })
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "bors"
            })
        elif pr_data['title'].startswith("[Merged by Bors]"):
            if has_peace_sign:
                client.remove_reaction({
                    "message_id": message['id'],
                    "emoji_name": "peace_sign"
                })
            if has_bors:
                client.remove_reaction({
                    "message_id": message['id'],
                    "emoji_name": "bors"
                })
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "merge"
            })
