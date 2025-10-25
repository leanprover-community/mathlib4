#!/usr/bin/env python3
"""
Aristotle API integration for automated theorem proving in Mathlib.

This script submits Lean files to the Aristotle API for automated proof generation.
Results are saved to a file with the .aristotle.lean suffix.
"""

import argparse
import asyncio
import os
import sys
from pathlib import Path
from typing import Optional

try:
    import aristotlelib
except ImportError:
    print("Error: aristotlelib is not installed.", file=sys.stderr)
    print("Install it with: pip install aristotlelib", file=sys.stderr)
    sys.exit(1)


def find_project_root() -> Optional[Path]:
    """Find the project root by looking for .git directory."""
    current = Path.cwd()
    while current != current.parent:
        if (current / ".git").exists():
            return current
        current = current.parent
    return None


def read_config_file(config_path: Path) -> Optional[str]:
    """Read API key from a config file."""
    if not config_path.exists():
        return None

    try:
        content = config_path.read_text().strip()
        # Support simple formats:
        # 1. Just the key itself
        # 2. ARISTOTLE_API_KEY=key
        # 3. api_key=key
        for line in content.split('\n'):
            line = line.strip()
            if not line or line.startswith('#'):
                continue

            # Direct key (starts with arstl_)
            if line.startswith('arstl_'):
                return line

            # Key=value format
            if '=' in line:
                key, value = line.split('=', 1)
                key = key.strip()
                value = value.strip().strip('"').strip("'")
                if key.upper() in ['ARISTOTLE_API_KEY', 'API_KEY']:
                    return value

        return None
    except Exception:
        return None


def get_api_key() -> str:
    """Get the Aristotle API key from environment or config files.

    Priority order:
    1. ARISTOTLE_API_KEY environment variable
    2. .aristotle.conf in project root
    3. ~/.config/aristotle/config
    """
    # 1. Check environment variable
    api_key = os.environ.get("ARISTOTLE_API_KEY")
    if api_key:
        return api_key

    # 2. Check project config
    project_root = find_project_root()
    if project_root:
        project_config = project_root / ".aristotle.conf"
        api_key = read_config_file(project_config)
        if api_key:
            return api_key

    # 3. Check user config
    user_config = Path.home() / ".config" / "aristotle" / "config"
    api_key = read_config_file(user_config)
    if api_key:
        return api_key

    # Not found anywhere
    print("Error: ARISTOTLE_API_KEY not found.", file=sys.stderr)
    print("\nYou can set your API key in one of these ways:", file=sys.stderr)
    print("\n1. Environment variable:", file=sys.stderr)
    print("     export ARISTOTLE_API_KEY='your-api-key-here'", file=sys.stderr)
    print("\n2. Project config file (.aristotle.conf in repo root):", file=sys.stderr)
    print("     echo 'ARISTOTLE_API_KEY=your-api-key-here' > .aristotle.conf", file=sys.stderr)
    print("\n3. User config file (~/.config/aristotle/config):", file=sys.stderr)
    print("     mkdir -p ~/.config/aristotle", file=sys.stderr)
    print("     echo 'ARISTOTLE_API_KEY=your-api-key-here' > ~/.config/aristotle/config", file=sys.stderr)
    sys.exit(1)


def validate_input_file(file_path: Path) -> None:
    """Validate that the input file exists and is a .lean file."""
    if not file_path.exists():
        print(f"Error: File not found: {file_path}", file=sys.stderr)
        sys.exit(1)

    if file_path.suffix != ".lean":
        print(f"Error: Input file must have .lean extension: {file_path}", file=sys.stderr)
        sys.exit(1)


async def prove_file(input_path: Path, output_path: Optional[Path], api_key: str) -> None:
    """Submit file to Aristotle API and save the result."""
    print(f"Submitting {input_path} to Aristotle API...")

    try:
        # Set the API key
        aristotlelib.set_api_key(api_key)

        # Submit the proof request and wait for completion
        print("\nSubmitting proof request and waiting for completion...")
        print("(This may take a few minutes...)")

        # If no custom output specified, put output in same directory as input
        if not output_path:
            output_path = input_path.parent / f"{input_path.stem}_aristotle.lean"

        result_path = await aristotlelib.Project.prove_from_file(
            input_file_path=str(input_path),
            output_file_path=str(output_path),
            wait_for_completion=True,
            polling_interval_seconds=5
        )

        print(f"\n✓ Proof generation completed successfully!")
        print(f"✓ Proof written to: {result_path}")

    except Exception as e:
        print(f"\n✗ Error communicating with Aristotle API: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        sys.exit(1)


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Submit Lean files to Aristotle API for automated proof generation.",
        epilog="Example: python3 scripts/aristotle/prove.py Mathlib/Analysis/Deriv.lean"
    )
    parser.add_argument(
        "input_file",
        type=Path,
        help="Path to the input .lean file"
    )
    parser.add_argument(
        "-o", "--output",
        type=str,
        default=None,
        help="Output file path (default: same directory as input, with _aristotle suffix)"
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Enable verbose output"
    )

    args = parser.parse_args()

    # Validate input
    validate_input_file(args.input_file)

    # Get API key
    api_key = get_api_key()

    # Convert output to Path if specified
    output_path = Path(args.output) if args.output else None

    # Run the async proof generation
    asyncio.run(prove_file(args.input_file, output_path, api_key))


if __name__ == "__main__":
    main()
