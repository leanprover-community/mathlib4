#!/usr/bin/env python3
"""
Script to find GitHub issue/PR URLs in the codebase and check their status.
"""

import os
import re
import sys
from pathlib import Path
from typing import List, Tuple, Dict, Set
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock
import fnmatch

def load_gitignore_patterns(root_dir: str) -> Set[str]:
    """Load patterns from .gitignore file."""
    gitignore_path = os.path.join(root_dir, '.gitignore')
    patterns = set()
    
    # Add common directories that should always be ignored
    # These are directories that commonly contain vendored code or build artifacts
    patterns.update(['venv', 'venv*', '.venv', 'env', '.env', '__pycache__', 
                     'node_modules', '.git', 'target', 'build', 'dist', '*.egg-info',
                     '.lake', '.cache', 'lake-packages'])
    
    if os.path.exists(gitignore_path):
        try:
            with open(gitignore_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    # Skip comments and empty lines
                    if line and not line.startswith('#'):
                        # Handle directory patterns
                        if line.endswith('/'):
                            patterns.add(line[:-1])
                        else:
                            patterns.add(line)
        except IOError:
            pass
    
    return patterns

def should_skip_dir(dir_name: str, dir_path: str, root_dir: str, gitignore_patterns: Set[str]) -> bool:
    """Check if a directory should be skipped based on gitignore patterns."""
    # Always skip hidden directories
    if dir_name.startswith('.'):
        return True
    
    # Check against gitignore patterns
    for pattern in gitignore_patterns:
        # Simple pattern matching (not full gitignore syntax, but covers common cases)
        if fnmatch.fnmatch(dir_name, pattern):
            return True
        # Check relative path patterns
        rel_path = os.path.relpath(dir_path, root_dir)
        if fnmatch.fnmatch(rel_path, pattern):
            return True
    
    return False

def find_github_urls(root_dir: str) -> List[Tuple[str, str, int, str]]:
    """Find all GitHub issue/PR URLs in the codebase with line numbers and context."""
    pattern = re.compile(r'https://github\.com/([^/\s]+)/([^/\s]+)/(issues?|pull|pulls)/(\d+)')
    results = []
    gitignore_patterns = load_gitignore_patterns(root_dir)
    
    for root, dirs, files in os.walk(root_dir):
        # Filter directories based on gitignore patterns
        dirs[:] = [d for d in dirs if not should_skip_dir(d, os.path.join(root, d), root_dir, gitignore_patterns)]
        
        for file in files:
            # Skip binary and non-text files
            if file.endswith(('.pyc', '.pyo', '.exe', '.dll', '.so', '.dylib', '.jar', '.class', '.zip', '.tar', '.gz')):
                continue
                
            file_path = os.path.join(root, file)
            try:
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                    # Calculate line numbers
                    lines = content.split('\n')
                    line_starts = [0]
                    for line in lines[:-1]:
                        line_starts.append(line_starts[-1] + len(line) + 1)  # +1 for newline
                    
                    for match in pattern.finditer(content):
                        url = match.group(0)
                        # Find line number
                        match_pos = match.start()
                        line_num = 1
                        for i, start_pos in enumerate(line_starts):
                            if start_pos <= match_pos:
                                line_num = i + 1
                            else:
                                break
                        
                        # Extract context if URL is in a comment
                        context = ""
                        if line_num <= len(lines):
                            current_line = lines[line_num - 1].strip()
                            if current_line.startswith('--'):
                                # Find contiguous block of comment lines
                                start_line = line_num - 1
                                end_line = line_num - 1
                                
                                # Go backwards to find start of comment block
                                while start_line > 0 and lines[start_line - 1].strip().startswith('--'):
                                    start_line -= 1
                                
                                # Go forwards to find end of comment block
                                while end_line < len(lines) - 1 and lines[end_line + 1].strip().startswith('--'):
                                    end_line += 1
                                
                                # Extract the comment block
                                comment_lines = []
                                for i in range(start_line, end_line + 1):
                                    line = lines[i].strip()
                                    if line.startswith('--'):
                                        # Remove leading -- and optional space
                                        cleaned = line[2:].lstrip(' ')
                                        comment_lines.append(cleaned)
                                
                                context = ' '.join(comment_lines).strip()
                                # Limit context length
                                if len(context) > 200:
                                    context = context[:197] + "..."
                        
                        # Get relative path for cleaner output
                        rel_path = os.path.relpath(file_path, root_dir)
                        results.append((rel_path, url, line_num, context))
            except (OSError, IOError):
                continue
    
    return results

def check_url_status(url: str) -> Dict[str, any]:
    """Check if a GitHub issue/PR is closed using gh CLI."""
    # Parse the URL
    match = re.match(r'https://github\.com/([^/]+)/([^/]+)/(issues?|pull|pulls)/(\d+)', url)
    if not match:
        return {"error": "Invalid URL format"}
    
    owner, repo, issue_type, number = match.groups()
    
    # Determine if it's a PR or issue - GitHub API uses "pulls" for PRs and "issues" for issues
    api_endpoint = "pulls" if "pull" in issue_type else "issues"
    
    try:
        # Use gh CLI to check status
        cmd = ["gh", "api", f"repos/{owner}/{repo}/{api_endpoint}/{number}", "--jq", ".state,.title"]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
        
        if result.returncode != 0:
            error_msg = result.stderr.strip()
            # If it's a 404, try the alternate endpoint (issue vs PR)
            if "HTTP 404" in error_msg:
                # Try the opposite endpoint
                alt_endpoint = "issues" if api_endpoint == "pulls" else "pulls"
                cmd_alt = ["gh", "api", f"repos/{owner}/{repo}/{alt_endpoint}/{number}", "--jq", ".state,.title"]
                result_alt = subprocess.run(cmd_alt, capture_output=True, text=True, timeout=10)
                
                if result_alt.returncode == 0:
                    lines = result_alt.stdout.strip().split('\n')
                    if len(lines) >= 2:
                        state = lines[0]
                        title = lines[1] if len(lines) > 1 else "Unknown"
                        # Note that the URL type is wrong
                        actual_type = "issue" if alt_endpoint == "issues" else "PR"
                        expected_type = "PR" if api_endpoint == "pulls" else "issue"
                        return {"state": state, "title": title, 
                                "redirect": True,
                                "note": f"URL says {expected_type} but it's actually an {actual_type}"}
                    else:
                        return {"state": lines[0] if lines else "unknown", "title": "Unknown", "redirect": True}
                else:
                    # Both endpoints failed, it truly doesn't exist
                    return {"error": "Not found (404) - checked both issues and pulls"}
            elif "HTTP 403" in error_msg:
                return {"error": "Forbidden (403)"}
            elif "HTTP 401" in error_msg:
                return {"error": "Unauthorized (401)"}
            else:
                return {"error": error_msg[:50] if error_msg else "Failed"}
        
        lines = result.stdout.strip().split('\n')
        if len(lines) >= 2:
            state = lines[0]
            title = lines[1] if len(lines) > 1 else "Unknown"
            return {"state": state, "title": title}
        else:
            return {"state": lines[0] if lines else "unknown", "title": "Unknown"}
            
    except subprocess.TimeoutExpired:
        return {"error": "Timeout"}
    except FileNotFoundError:
        return {"error": "gh CLI not found - install with: brew install gh"}
    except Exception as e:
        return {"error": str(e)[:50]}

def update_progress(current: int, total: int, message: str = ""):
    """Update progress counter in place."""
    # Clear the line and print progress
    sys.stdout.write('\r')  # Move to beginning of line
    sys.stdout.write(f"Checking URLs: {current}/{total} ({current*100//total}%)")
    if message:
        sys.stdout.write(f" - {message[:30]}")  # Limit message length
    # Pad with spaces to clear any remaining text
    sys.stdout.write(' ' * 20)
    sys.stdout.flush()

def main():
    root_dir = os.getcwd()
    
    # Find all URLs
    url_pairs = find_github_urls(root_dir)
    
    # Remove duplicates while preserving order
    seen = set()
    unique_pairs = []
    for pair in url_pairs:
        if pair not in seen:
            seen.add(pair)
            unique_pairs.append(pair)
    
    # Group by URL to check each unique URL only once
    url_to_files = {}
    for file_path, url, line_num, context in unique_pairs:
        if url not in url_to_files:
            url_to_files[url] = []
        url_to_files[url].append((file_path, line_num, context))
    
    total_urls = len(url_to_files)
    
    # Prepare results storage
    results = []
    completed_count = 0
    lock = Lock()
    
    def check_and_store(url: str, files: List[Tuple[str, int, str]]) -> List[Dict]:
        """Check URL and prepare results for all files referencing it."""
        status = check_url_status(url)
        return [{"file": f"{file_path}:{line_num}", "url": url, "status": status, "context": context} 
                for file_path, line_num, context in files]
    
    # Use ThreadPoolExecutor for parallel checking
    # Limit workers to avoid hitting rate limits too hard
    max_workers = min(10, total_urls)  # Max 10 parallel requests
    
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        # Submit all tasks
        future_to_url = {
            executor.submit(check_and_store, url, files): url 
            for url, files in url_to_files.items()
        }
        
        # Process completed tasks
        for future in as_completed(future_to_url):
            with lock:
                completed_count += 1
                update_progress(completed_count, total_urls)
            
            try:
                url_results = future.result()
                results.extend(url_results)
            except Exception as e:
                url = future_to_url[future]
                # Add error result for this URL
                for file_path, line_num, context in url_to_files[url]:
                    results.append({
                        "file": f"{file_path}:{line_num}",
                        "url": url,
                        "status": {"error": str(e)[:50]},
                        "context": context
                    })
    
    # Clear the progress line and add newline
    sys.stdout.write('\r' + ' ' * 100 + '\r')  # Clear entire line
    sys.stdout.flush()
    
    # Print results
    print("="*80)
    print("RESULTS")
    print("="*80 + "\n")
    
    # Group results by status
    closed_items = []
    open_items = []
    error_items = []
    redirect_items = []
    
    for item in results:
        if "error" in item["status"]:
            error_items.append(item)
        elif item["status"].get("redirect", False):
            redirect_items.append(item)
            # Also categorize by state
            if item["status"].get("state", "").lower() == "closed":
                closed_items.append(item)
            else:
                open_items.append(item)
        elif item["status"].get("state", "").lower() == "closed":
            closed_items.append(item)
        else:
            open_items.append(item)
    
    # Print closed items
    if closed_items:
        print(f"CLOSED Issues/PRs ({len(closed_items)} references):")
        print("-" * 40)
        for item in closed_items:
            print(f"File: {item['file']}")
            print(f"URL:  {item['url']}")
            print(f"Title: {item['status'].get('title', 'Unknown')}")
            if 'note' in item['status']:
                print(f"Note: {item['status']['note']}")
            if item.get('context'):
                print(f"Context: {item['context']}")
            print()
    
    # Print open items (optional - comment out if too verbose)
    if open_items and len(open_items) <= 20:  # Only show if not too many
        print(f"\nOPEN Issues/PRs ({len(open_items)} references):")
        print("-" * 40)
        for item in open_items[:20]:  # Limit to first 20
            print(f"File: {item['file']}")
            print(f"URL:  {item['url']}")
            print(f"Title: {item['status'].get('title', 'Unknown')}")
            if 'note' in item['status']:
                print(f"Note: {item['status']['note']}")
            if item.get('context'):
                print(f"Context: {item['context']}")
            print()
        if len(open_items) > 20:
            print(f"... and {len(open_items) - 20} more open issues/PRs")
    elif open_items:
        print(f"\nOPEN Issues/PRs: {len(open_items)} references (use --show-open to display)")
    
    # Print redirects
    if redirect_items:
        print(f"\nREDIRECT URLs ({len(redirect_items)} references):")
        print("-" * 40)
        for item in redirect_items:
            print(f"File: {item['file']}")
            print(f"URL:  {item['url']}")
            print(f"Title: {item['status'].get('title', 'Unknown')}")
            print(f"Status: {item['status'].get('state', 'Unknown')}")
            if 'note' in item['status']:
                print(f"Note: {item['status']['note']}")
            if item.get('context'):
                print(f"Context: {item['context']}")
            print()
    
    # Print errors
    if error_items:
        print(f"\nERRORS ({len(error_items)} references):")
        print("-" * 40)
        # Group errors by error message for cleaner output
        error_groups = {}
        for item in error_items:
            error_msg = item["status"].get("error", "Unknown error")
            if error_msg not in error_groups:
                error_groups[error_msg] = []
            error_groups[error_msg].append(item)
        
        for error_msg, items in error_groups.items():
            print(f"\nError: {error_msg} ({len(items)} occurrences)")
            for item in items:  # Show all errors
                print(f"  - {item['url']} in {item['file']}")
                if item.get('context'):
                    print(f"    Context: {item['context']}")
    
    # Summary
    print("\n" + "="*80)
    print("SUMMARY")
    print("="*80)
    print(f"Total file/URL pairs found: {len(results)}")
    print(f"Unique URLs checked: {total_urls}")
    print(f"Closed issues/PRs: {len(closed_items)} references")
    print(f"Open issues/PRs: {len(open_items)} references")
    print(f"Redirect URLs: {len(redirect_items)} references")
    print(f"Errors: {len(error_items)} references")
    
    # Suggest actions
    if closed_items:
        print(f"\n💡 Found {len(closed_items)} references to closed issues/PRs that could potentially be cleaned up.")
    if redirect_items:
        print(f"🔀 Found {len(redirect_items)} URLs that redirect (wrong URL type - should be fixed).")

if __name__ == "__main__":
    main()