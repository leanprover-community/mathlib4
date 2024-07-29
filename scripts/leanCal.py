import sys
from datetime import datetime, timedelta, timezone
import requests
from icalendar import Calendar

if len(sys.argv) != 2:
    print("Expected exactly one command line argument: the calendar url")
    sys.exit(1)
else:
    url = sys.argv[1]

cal = Calendar.from_ical(requests.get(url).text)

# we compute the current time once and for all. 
# Hopefully the whole script is fast enough
now: datetime = datetime.now(tz=timezone.utc)

week = timedelta(weeks=1)
day = timedelta(days=1)
hour = timedelta(hours=1)
# epsilon should be less than the polling interval.
# Here we assume the calendar will be polled every 15 minutes. 
epsilon = timedelta(minutes=10)

def timely(date: datetime, delta: timedelta) -> bool:
    return date > now + delta and date < now + delta + epsilon

def collect_msg(cal: Calendar) -> list[str]:
    messages: list[str] = []
    for event in cal.walk("VEVENT"):
        start: datetime = event.decoded("dtstart")
        description: str = event.get("summary")
        msg: str = f"{description} at <time:{start.isoformat()}>"
        if timely(start, week):
            messages.append(f"**Reminder**: {msg}")
        elif timely(start, day):
            messages.append(f"**Short term reminder**: {msg}")
        elif timely(start, hour):
            messages.append(f"**Urgent reminder**: {msg}")
    return messages

print("\n".join(collect_msg(cal)))
