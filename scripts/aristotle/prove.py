#!/usr/bin/env python3
"""
Aristotle API integration for automated theorem proving in Mathlib.

This script submits Lean files to the Aristotle API for automated proof generation.
Results are saved to a file with the .aristotle.lean suffix.
"""

import argparse
import asyncio
import os
from pathlib import Path
from typing import Optional

try:
    import aristotlelib
except ImportError:
    raise SystemExit(
        "Error: aristotlelib is not installed.\n"
        "Install it with: pip install aristotlelib"
    )


def find_project_root() -> Optional[Path]:
    """Find the project root by looking for .git directory."""
    current = Path.cwd()
    while current != current.parent:
        if (current / ".git").exists():
            return current
        current = current.parent
    return None


def read_config_file(config_path: Path) -> Optional[str]:
    """Read API key from a config file.

    Supports:
    - Direct key: arstl_...
    - Key=value: ARISTOTLE_API_KEY=...
    """
    if not config_path.exists():
        return None

    try:
        for line in config_path.read_text().splitlines():
            line = line.strip()
            if not line or line.startswith('#'):
                continue

            if line.startswith('arstl_'):
                return line

            if '=' in line:
                key, _, value = line.partition('=')
                if key.strip().upper() in ['ARISTOTLE_API_KEY', 'API_KEY']:
                    return value.strip().strip('"').strip("'")

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
    if api_key := os.environ.get("ARISTOTLE_API_KEY"):
        return api_key

    if project_root := find_project_root():
        if api_key := read_config_file(project_root / ".aristotle.conf"):
            return api_key

    if api_key := read_config_file(Path.home() / ".config" / "aristotle" / "config"):
        return api_key

    raise SystemExit(
        "Error: ARISTOTLE_API_KEY not found.\n"
        "\n"
        "You can set your API key in one of these ways:\n"
        "\n"
        "1. Environment variable:\n"
        "     export ARISTOTLE_API_KEY='your-api-key-here'\n"
        "\n"
        "2. Project config file (.aristotle.conf in repo root):\n"
        "     echo 'ARISTOTLE_API_KEY=your-api-key-here' > .aristotle.conf\n"
        "\n"
        "3. User config file (~/.config/aristotle/config):\n"
        "     mkdir -p ~/.config/aristotle\n"
        "     echo 'ARISTOTLE_API_KEY=your-api-key-here' > ~/.config/aristotle/config"
    )


def validate_input_file(file_path: Path) -> None:
    """Validate that the input file exists and is a .lean file."""
    if not file_path.exists():
        raise SystemExit(f"Error: File not found: {file_path}")

    if file_path.suffix != ".lean":
        raise SystemExit(f"Error: Input file must have .lean extension: {file_path}")


async def prove_file(input_path: Path, output_path: Optional[Path], api_key: str) -> None:
    """Submit file to Aristotle API and save the result."""
    print(f"Submitting {input_path} to Aristotle API...")

    try:
        aristotlelib.set_api_key(api_key)

        print("\nSubmitting proof request and waiting for completion...")
        print("(This may take a few minutes...)")

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
        raise SystemExit(f"Error communicating with Aristotle API: {e}")


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
        type=Path,
        help="Output file path (default: same directory as input, with _aristotle suffix)"
    )

    args = parser.parse_args()

    validate_input_file(args.input_file)
    api_key = get_api_key()

    asyncio.run(prove_file(args.input_file, args.output, api_key))


if __name__ == "__main__":
    main()
