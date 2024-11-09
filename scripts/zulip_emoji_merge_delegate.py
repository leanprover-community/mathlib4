#!/usr/bin/env python3
import sys
import zulip
import requests
import re

# Usage:
# python scripts/zulip_emoji_merge_delegate.py $ZULIP_API_KEY $ZULIP_EMAIL $ZULIP_SITE $GITHUB_TOKEN

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

# Fetch messages from the past 1h15
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
        has_merge = any(reaction['emoji_name'] == 'merge' for reaction in reactions)
        has_peace_sign = any(reaction['emoji_name'] == 'peace_sign' for reaction in reactions)

        if not has_merge and not has_peace_sign:
            pr_url = f"https://api.github.com/repos/leanprover-community/mathlib4/pulls/{pr_number}"
            pr_response = requests.get(pr_url, headers={"Authorization": GITHUB_TOKEN})
            pr_data = pr_response.json()

            if pr_data['title'].startswith("[Merged by Bors]"):
                client.add_reaction({
                    "message_id": message['id'],
                    "emoji_name": "merge"
                })
            elif 'delegated' in [label['name'] for label in pr_data['labels']]:
                client.add_reaction({
                    "message_id": message['id'],
                    "emoji_name": "peace_sign"
                })
