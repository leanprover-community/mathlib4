#!/usr/bin/env python3
import sys
import zulip
import re

# Usage:
# python scripts/zulip_emoji_merge_delegate.py $ZULIP_API_KEY $ZULIP_EMAIL $ZULIP_SITE $LABEL $PR_NUMBER
# See .github/workflows/zulip_emoji_merge_delegate.yaml for the meaning of these variables

ZULIP_API_KEY = sys.argv[1]
ZULIP_EMAIL = sys.argv[2]
ZULIP_SITE = sys.argv[3]
LABEL = sys.argv[4]
PR_NUMBER = sys.argv[5]

print(f"LABEL: '{LABEL}'")
print(f"PR_NUMBER: '{PR_NUMBER}'")

# Initialize Zulip client
client = zulip.Client(
    email=ZULIP_EMAIL,
    api_key=ZULIP_API_KEY,
    site=ZULIP_SITE
)

# Fetch the messages containing the PR number from the public channels.
# There does not seem to be a way to search simultaneously public and private channels.
public_response = client.get_messages({
    "anchor": "newest",
    "num_before": 5000,
    "num_after": 0,
    "narrow": [
        {"operator": "channels", "operand": "public"},
        {"operator": "search", "operand": f'#{PR_NUMBER}'},
    ],
})

# Fetch the messages containing the PR number from the `mathlib reviewers` channel
# There does not seem to be a way to search simultaneously public and private channels.
reviewers_response = client.get_messages({
    "anchor": "newest",
    "num_before": 5000,
    "num_after": 0,
    "narrow": [
        {"operator": "channel", "operand": "mathlib reviewers"},
        {"operator": "search", "operand": f'#{PR_NUMBER}'},
    ],
})

print(f"public_response:{public_response}")
print(f"reviewers_response:{reviewers_response}")

# Get the oldest message in any topic in `PR reviews` whose title matches `#{PR_NUMBER}`.
first_message_in_PR_reviews = client.get_messages({
    "anchor": "oldest",
    "num_before": 0,
    "num_after": 1,
    "narrow": [
        {"operator": "channel", "operand": "PR reviews"},
        {"operator": "search", "operand": f'#{PR_NUMBER}'},
    ],
})
print(f'First message:{first_message_in_PR_reviews}')

messages = (public_response['messages']) + (reviewers_response['messages']) + (first_message_in_PR_reviews['messages'])

print(messages)
# we use the ID of the first message in the `PR reviews` channel to react to it
# whether or not it has the PR number in the content.
first_message_in_PR_reviews_id=messages[0]['id']
print(f'First message ID: {first_message_in_PR_reviews_id}')

pr_pattern = re.compile(f'https://github.com/leanprover-community/mathlib4/pull/{PR_NUMBER}')

print(f"Searching for: '{pr_pattern}'")

for message in messages:
    if message['display_recipient'] == 'rss':
        continue
    content = message['content']
    # Check for emoji reactions
    reactions = message['reactions']
    has_peace_sign = any(reaction['emoji_name'] == 'peace_sign' for reaction in reactions)
    has_bors = any(reaction['emoji_name'] == 'bors' for reaction in reactions)
    has_merge = any(reaction['emoji_name'] == 'merge' for reaction in reactions)
    has_awaiting_author = any(reaction['emoji_name'] == 'writing' for reaction in reactions)
    has_closed = any(reaction['emoji_name'] == 'closed-pr' for reaction in reactions)
    match = pr_pattern.search(content) or message['id'] == first_message_in_PR_reviews_id
    if match:
        print(f"matched: '{message}'")

        # removing previous emoji reactions
        # if the emoji is a custom emoji, add the fields `emoji_code` and `reaction_type` as well
        print("Removing previous reactions, if present.")
        if has_peace_sign:
            print('Removing peace_sign')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": "peace_sign"
            })
            print(f"result: '{result}'")
        if has_bors:
            print('Removing bors')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": "bors",
                "emoji_code": "22134",
                "reaction_type": "realm_emoji",
            })
            print(f"result: '{result}'")
        if has_merge:
            print('Removing merge')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": "merge"
            })
            print(f"result: '{result}'")
        if has_awaiting_author:
            print('Removing awaiting-author')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": "writing"
            })
            print(f"result: '{result}'")
        if has_closed:
            print('Removing closed-pr')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": "closed-pr",
                "emoji_code": "61293",  # 61282 was the earlier version of the emoji
                "reaction_type": "realm_emoji",
            })
            print(f"result: '{result}'")


        # applying appropriate emoji reaction
        print("Applying reactions, as appropriate.")
        if 'ready-to-merge' == LABEL:
            print('adding ready-to-merge')
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "bors"
            })
        elif 'delegated' == LABEL:
            print('adding delegated')
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "peace_sign"
            })
        elif LABEL == 'labeled':
            print('adding awaiting-author')
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "writing"
            })
        elif LABEL == 'closed':
            print('adding closed-pr')
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "closed-pr"
            })
        elif LABEL == 'unlabeled':
            print('awaiting-author removed')
            # the reaction was already removed.
        elif LABEL.startswith("[Merged by Bors]"):
            print('adding [Merged by Bors]')
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "merge"
            })
