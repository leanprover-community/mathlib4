#\!/usr/bin/env python3

import re
import sys
import os
from pathlib import Path

def normalize_spacing(text):
    """Remove extra spaces and ensure single spaces between words."""
    return ' '.join(word for word in text.split() if word)

def process_file(file_path):
    # Read the file
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original = content  # Save original content
    changed = False     # Track if we've made changes
    
    # Counters for report
    paren_count = 0
    brace_count = 0
    
    # Process the file until no more changes
    while True:
        old_content = content
        
        # Handle parenthesized declarations: (A : Type*) (B : Type*)
        pattern = r'\(([^:()\{\}]+)\s*:\s*Type\*\)\s*\(([^:()\{\}]+)\s*:\s*Type\*\)'
        match = re.search(pattern, content)
        if match:
            # Clean up variables by removing extra spaces
            var1 = normalize_spacing(match.group(1))
            var2 = normalize_spacing(match.group(2))
            
            # Create replacement with exactly one space between variables
            replacement = f'({var1} {var2} : Type*)'
            
            # Replace in the content
            content = content[:match.start()] + replacement + content[match.end():]
            paren_count += 1
            changed = True
            continue
        
        # Handle braced declarations: {A : Type*} {B : Type*}
        pattern = r'\{([^:()\{\}]+)\s*:\s*Type\*\}\s*\{([^:()\{\}]+)\s*:\s*Type\*\}'
        match = re.search(pattern, content)
        if match:
            # Clean up variables by removing extra spaces
            var1 = normalize_spacing(match.group(1))
            var2 = normalize_spacing(match.group(2))
            
            # Create replacement with exactly one space between variables
            replacement = f'{{{var1} {var2} : Type*}}'
            
            # Replace in the content
            content = content[:match.start()] + replacement + content[match.end():]
            brace_count += 1
            changed = True
            continue
        
        # If no changes in this iteration, we're done
        if content == old_content:
            break
    
    # Write changes back to file if we made any
    if changed:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content)
        print(f"Modified {file_path}: {paren_count} paren groups, {brace_count} brace groups")
        
    return (paren_count, brace_count)

def main():
    if len(sys.argv) < 2:
        print("Usage: python fix_types.py <file_or_directory>")
        sys.exit(1)
    
    target = sys.argv[1]
    
    if os.path.isfile(target):
        # Process single file
        process_file(target)
    else:
        # Process all .lean files recursively
        total_paren = 0
        total_brace = 0
        file_count = 0
        
        for file_path in Path(target).glob('**/*.lean'):
            try:
                paren, brace = process_file(str(file_path))
                if paren > 0 or brace > 0:
                    file_count += 1
                    total_paren += paren
                    total_brace += brace
            except Exception as e:
                print(f"Error processing {file_path}: {e}")
        
        print(f"\nSummary: Modified {file_count} files")
        print(f"Total replacements: {total_paren} parenthesized groups, {total_brace} braced groups")

if __name__ == '__main__':
    main()
