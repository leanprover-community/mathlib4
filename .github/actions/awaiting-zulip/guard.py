"""Enforce the awaiting-zulip label using trusted workflow code and read-only Zulip access."""

import base64
import datetime
import json
import os
import re
import sys
import time
from html.parser import HTMLParser
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import unquote, urlencode, urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener

LABEL = "awaiting-zulip"
REPO = "leanprover-community/mathlib4"
SITE = "https://leanprover.zulipchat.com"
EMAIL = "github-mathlib4-bot@leanprover.zulipchat.com"
MARKER = "<!-- awaiting-zulip-link-check -->"


class Unavailable(Exception):
    """Verification is inconclusive: leave the label alone and retry later."""


class MutationFailed(Exception):
    """A GitHub write failed; report it without claiming the label is unchanged."""


class NoRedirects(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None  # Never forward API credentials to a redirect destination.


class API:
    def __init__(self, base, authorization):
        self.base = base
        self.authorization = authorization
        self.opener = build_opener(NoRedirects())

    def call(self, path, *, params=None, data=None, method="GET"):
        url = self.base + path
        if params:
            url += "?" + urlencode(params)
        body = None if data is None else json.dumps(data).encode()
        headers = {
            "Authorization": self.authorization,
            "Accept": "application/json",
            "Content-Type": "application/json",
            "User-Agent": "mathlib-awaiting-zulip",
        }
        for attempt in range(3):
            try:
                with self.opener.open(
                    Request(url, body, headers, method=method), timeout=30
                ) as r:
                    raw = r.read()
                result = json.loads(raw) if raw else None
                if isinstance(result, dict) and result.get("result") == "error":
                    raise Unavailable("Zulip returned an API error")
                return result
            except HTTPError as e:
                if method == "DELETE" and e.code == 404:
                    return None
                if method == "GET" and (e.code == 429 or e.code >= 500) and attempt < 2:
                    time.sleep(2**attempt)
                    continue
                # Do not print response bodies, private topics, or credentials.
                error = Unavailable if method == "GET" else MutationFailed
                raise error(f"API request failed (HTTP {e.code})") from None
            except (URLError, TimeoutError, ValueError):
                if method == "GET" and attempt < 2:
                    time.sleep(2**attempt)
                    continue
                error = Unavailable if method == "GET" else MutationFailed
                raise error("API request failed or returned invalid JSON") from None
        raise Unavailable("API retries exhausted")

    def pages(self, path, **params):
        result = []
        page = 1
        while True:
            batch = self.call(path, params={**params, "per_page": 100, "page": page})
            result.extend(batch)
            if len(batch) < 100:
                return result
            page += 1


def directive(body):
    """Match the existing bot's whole-line syntax, with last directive winning."""
    found = [
        line.strip()
        for line in body.splitlines()
        if line.strip() in (LABEL, "-" + LABEL)
    ]
    return found[-1] if found else None


class Links(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.urls = []

    def handle_starttag(self, tag, attrs):
        if tag == "a":
            self.urls.extend(value for key, value in attrs if key == "href" and value)


def references_pr(message, number, repo=REPO):
    """Zulip expands URLs and linkifiers into the same rendered link destinations."""
    parser = Links()
    parser.feed(message["content"])
    urls = parser.urls + re.findall(r'https?://[^\s<>"`]+', message.get("subject", ""))
    urls += [
        link["url"] if isinstance(link, dict) else link
        for link in message.get("topic_links", message.get("subject_links", []))
    ]
    pattern = rf"/{re.escape(repo)}/(?:pull|issues)/{number}(?:/|$)"
    for url in urls:
        try:
            parts = urlsplit(url)
        except ValueError:
            continue
        if (
            parts.scheme in ("https", "http")
            and parts.netloc.lower() == "github.com"
            and re.match(pattern, parts.path, re.IGNORECASE)
        ):
            return True
    return False


def zulip_urls(texts):
    urls = set()
    for text in texts:
        parser = Links()
        parser.feed(text)
        candidates = parser.urls + re.findall(r'https?://[^\s<>"`]+', text)
        for url in candidates:
            url = url.rstrip(".,;:!?)]}")
            try:
                parts = urlsplit(url)
            except ValueError:
                continue
            if (
                parts.scheme == "https"
                and parts.netloc == urlsplit(SITE).netloc
                and (
                    re.search(r"/(?:near|with)/\d+(?:/|$)", parts.fragment)
                    or re.search(r"/(?:stream|channel)/\d+[^/]*/topic/", parts.fragment)
                )
            ):
                urls.add(url)
    return sorted(urls)


def decode_topic(value):
    # Zulip encodes UTF-8 bytes using .XX, older links can also contain %XX.
    value = unquote(value)
    return re.sub(
        r"(?:\.[0-9a-fA-F]{2})+",
        lambda m: bytes.fromhex(m[0].replace(".", "")).decode("utf-8"),
        value,
    )


class Zulip:
    def __init__(self, api):
        self.api = api
        self.anchors = {}
        self.topics = {}

    def topic(self, url):
        fragment = urlsplit(url).fragment
        anchor = re.search(r"/(?:near|with)/(\d+)(?:/|$)", fragment)
        if anchor:
            message_id = anchor[1]
            if message_id not in self.anchors:
                self.anchors[message_id] = self.api.call("/messages/" + message_id)[
                    "message"
                ]
            message = self.anchors[message_id]
            if message["type"] != "stream":
                raise Unavailable(
                    "The discussion link does not identify a channel topic"
                )
            # The anchor is authoritative even if the topic has been renamed or moved.
            return message["stream_id"], message["subject"]
        stream = re.search(r"/(?:stream|channel)/(\d+)[^/]*/topic/([^/]+)", fragment)
        if not stream:
            raise Unavailable("Cannot resolve discussion link")
        return int(stream[1]), decode_topic(stream[2])

    def messages(self, topic):
        if topic not in self.topics:
            narrow = [
                {"operator": "channel", "operand": topic[0]},
                {"operator": "topic", "operand": topic[1]},
            ]
            messages = []
            anchor = "oldest"
            while True:
                data = self.api.call(
                    "/messages",
                    params={
                        "narrow": json.dumps(narrow),
                        "anchor": anchor,
                        "num_before": 0,
                        "num_after": 1000,
                        "include_anchor": "false",
                        "apply_markdown": "true",
                    },
                )
                batch = data["messages"]
                messages.extend(batch)
                if data.get("found_newest"):
                    break
                if not batch or batch[-1]["id"] == anchor:
                    raise Unavailable("Could not read the complete discussion")
                anchor = batch[-1]["id"]
            self.topics[topic] = messages
        return self.topics[topic]

    def qualifies(self, urls, number):
        unavailable = False
        for url in urls:
            try:
                if any(
                    references_pr(m, number) for m in self.messages(self.topic(url))
                ):
                    return True
            except (Unavailable, KeyError, UnicodeError, ValueError):
                unavailable = True
        if unavailable:
            raise Unavailable("At least one linked discussion could not be verified")
        return False


def request_comment(event):
    return event.get("comment") or event.get("review") or {}


def label_event(events):
    matching = [
        e
        for e in events
        if e.get("event") in ("labeled", "unlabeled")
        and e.get("label", {}).get("name") == LABEL
    ]
    return matching[-1] if matching else None


def labeler(event, comments):
    actor = event.get("actor") or {}
    if actor.get("type") != "Bot":
        return actor.get("login")
    # Older comment-labeling runs appear as github-actions[bot] in label history.
    # Attribute them to the preceding directive, not an unrelated recent commenter.
    applied = datetime.datetime.fromisoformat(event["created_at"])
    candidates = []
    for c in comments:
        if (
            directive(c.get("body") or "") != LABEL
            or c.get("user", {}).get("type") == "Bot"
        ):
            continue
        stamp = c.get("submitted_at") or c.get("created_at")
        if stamp:
            age = (applied - datetime.datetime.fromisoformat(stamp)).total_seconds()
            # Hosted jobs may queue for hours before the bot applies the label.
            if 0 <= age <= 24 * 60 * 60:
                candidates.append((age, c["user"]["login"]))
    return min(candidates)[1] if candidates else actor.get("login")


def notice(number, login, removed):
    greeting = f"@{login}, thanks" if login else "Thanks"
    action = (
        "I’ve removed the label for now to help keep this PR visible for review."
        if removed
        else "I haven’t applied the label yet, to help keep this PR visible for review."
    )
    return (
        f"{MARKER}\n{greeting} for flagging this for discussion! Please add a link in the "
        f"PR description or a comment to a Zulip conversation that mentions #{number}, "
        "then reapply `awaiting-zulip`.\n\n"
        f"In Zulip, you can reference this PR using `#{number}` or its full GitHub URL. "
        "If you’ve already linked a conversation, please make sure it contains that reference.\n\n"
        f"{action}"
    )


class Guard:
    def __init__(self, github, zulip, dry_run=False):
        self.github = github
        self.zulip = zulip
        self.dry_run = dry_run

    def path(self, number, suffix=""):
        return f"/repos/{REPO}/issues/{number}{suffix}"

    def comments(self, number):
        issue_comments = self.github.pages(self.path(number, "/comments"))
        reviews = self.github.pages(f"/repos/{REPO}/pulls/{number}/reviews")
        inline = self.github.pages(f"/repos/{REPO}/pulls/{number}/comments")
        return issue_comments, issue_comments + reviews + inline

    def check(self, number, *, command=None, author=None):
        issue = self.github.call(self.path(number))
        if issue["state"] != "open" or "pull_request" not in issue:
            return
        present = any(l["name"] == LABEL for l in issue["labels"])
        if command == "-" + LABEL:
            if present and not self.dry_run:
                self.github.call(self.path(number, "/labels/" + LABEL), method="DELETE")
            return
        if not present and command != LABEL:
            return
        issue_comments, comments = self.comments(number)
        applied = (
            label_event(self.github.pages(self.path(number, "/events")))
            if present
            else None
        )
        urls = zulip_urls(
            [issue.get("body") or ""] + [c.get("body") or "" for c in comments]
        )
        valid = self.zulip.qualifies(urls, number)
        print(
            f"#{number}: {'valid discussion' if valid else 'missing qualifying discussion'}"
        )
        if valid:
            if command == LABEL and not present and not self.dry_run:
                self.github.call(
                    self.path(number, "/labels"),
                    method="POST",
                    data={"labels": [LABEL]},
                )
            return
        # Identify the actual labeler; abort if its lifecycle changes while checking Zulip.
        login = labeler(applied, comments) if applied else author
        body = notice(number, login, present)
        if self.dry_run:
            print(
                f"#{number}: would {'remove' if present else 'decline'} label and notify @{login}"
            )
            return
        latest_issue = self.github.call(self.path(number))
        if latest_issue.get("updated_at") != issue.get("updated_at"):
            print(
                f"#{number}: PR changed during verification; deferring to the next check"
            )
            return
        if present:
            current = label_event(self.github.pages(self.path(number, "/events")))
            if (
                not current
                or not applied
                or current["id"] != applied["id"]
                or current["event"] != "labeled"
            ):
                return
            self.github.call(self.path(number, "/labels/" + LABEL), method="DELETE")
        existing = next(
            (
                c
                for c in issue_comments
                if MARKER in (c.get("body") or "")
                and c.get("user", {}).get("login") == "github-actions[bot]"
            ),
            None,
        )
        if existing:
            if existing["body"] != body:
                self.github.call(
                    f"/repos/{REPO}/issues/comments/{existing['id']}",
                    method="PATCH",
                    data={"body": body},
                )
        else:
            self.github.call(
                self.path(number, "/comments"), method="POST", data={"body": body}
            )


def run():
    if os.environ.get("GITHUB_REPOSITORY") != REPO:
        raise ValueError("This action is configured only for " + REPO)
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    github = API("https://api.github.com", "Bearer " + os.environ["GH_TOKEN"])
    key = os.environ.get("ZULIP_API_KEY", "")
    authorization = "Basic " + base64.b64encode(f"{EMAIL}:{key}".encode()).decode()
    zulip = Zulip(API(SITE + "/api/v1", authorization))
    guard = Guard(github, zulip, os.environ.get("GUARD_DRY_RUN") == "true")
    mode = os.environ.get("GUARD_MODE", "enforce")
    if mode == "directive":
        comment = request_comment(event)
        command = directive(comment.get("body") or "")
        number = (event.get("issue") or event.get("pull_request") or {}).get("number")
        if command and number:
            guard.check(
                number,
                command=command,
                author=comment["user"]["login"],
            )
        return
    number = os.environ.get("GUARD_PR") or (
        event.get("issue") or event.get("pull_request") or {}
    ).get("number")
    if number:
        numbers = [int(number)]
    else:
        issues = github.pages(f"/repos/{REPO}/issues", state="open", labels=LABEL)
        numbers = [i["number"] for i in issues if "pull_request" in i]
    failures = []
    for number in numbers:
        try:
            guard.check(number)
        except Unavailable:
            # Continue the sweep; never treat an inaccessible topic as missing evidence.
            print(
                f"::warning::#{number}: verification unavailable; label left unchanged"
            )
            failures.append(number)
    if failures:
        raise Unavailable(
            "Verification unavailable for " + ", ".join(f"#{n}" for n in failures)
        )


if __name__ == "__main__":
    try:
        run()
    except (Unavailable, MutationFailed) as error:
        print(f"::error::{error}")
        sys.exit(1)
