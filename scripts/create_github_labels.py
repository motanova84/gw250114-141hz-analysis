#!/usr/bin/env python3
"""
Script to create required GitHub labels for Dependabot and workflows.

This script can be run manually if needed to create labels without triggering
the GitHub Actions workflow. Requires the `gh` CLI tool to be installed and
authenticated.

Usage:
    python scripts/create_github_labels.py
"""

import json
import subprocess
import sys

# Define all labels used in the repository
LABELS = [
    # Dependabot required labels
    {
        "name": "automated",
        "color": "0E8A16",
        "description": "Automated changes by bots (Dependabot, GitHub Actions)"
    },
    {
        "name": "dependencies",
        "color": "0366D6",
        "description": "Updates to project dependencies"
    },
    {
        "name": "github-actions",
        "color": "2088FF",
        "description": "Updates to GitHub Actions workflows"
    },
    {
        "name": "python",
        "color": "3776AB",
        "description": "Python-related changes"
    },
    # Issue type labels
    {
        "name": "bug",
        "color": "D73A4A",
        "description": "Something is not working correctly"
    },
    {
        "name": "enhancement",
        "color": "A2EEEF",
        "description": "New feature or request"
    },
    {
        "name": "documentation",
        "color": "0075CA",
        "description": "Improvements or additions to documentation"
    },
    {
        "name": "testing",
        "color": "FBCA04",
        "description": "Related to testing infrastructure"
    },
    {
        "name": "ci/cd",
        "color": "1D76DB",
        "description": "Continuous Integration/Deployment changes"
    },
    {
        "name": "security",
        "color": "B60205",
        "description": "Security-related issues or updates"
    },
    # Scientific category labels
    {
        "name": "frequency-analysis",
        "color": "5319E7",
        "description": "Related to 141.7001 Hz frequency analysis"
    },
    {
        "name": "gravitational-waves",
        "color": "7057FF",
        "description": "Gravitational wave data analysis"
    },
    {
        "name": "validation",
        "color": "BFD4F2",
        "description": "Data or method validation"
    },
    {
        "name": "statistics",
        "color": "D4C5F9",
        "description": "Statistical analysis or Bayesian methods"
    },
    # Priority labels
    {
        "name": "priority: high",
        "color": "D93F0B",
        "description": "High priority issue or PR"
    },
    # Process labels
    {
        "name": "stale",
        "color": "EDEDED",
        "description": "Issue or PR has been inactive for a long time"
    }
]


def check_gh_cli():
    """Check if gh CLI is installed and authenticated."""
    try:
        result = subprocess.run(
            ["gh", "auth", "status"],
            capture_output=True,
            text=True,
            check=False
        )
        if result.returncode != 0:
            print("❌ Error: gh CLI is not authenticated.")
            print("   Please run: gh auth login")
            return False
        return True
    except FileNotFoundError:
        print("❌ Error: gh CLI is not installed.")
        print("   Please install it from: https://cli.github.com/")
        return False


def create_or_update_label(label):
    """Create or update a GitHub label."""
    name = label["name"]
    color = label["color"]
    description = label["description"]
    
    # Try to update the label first
    result = subprocess.run(
        [
            "gh", "label", "edit", name,
            "--color", color,
            "--description", description
        ],
        capture_output=True,
        text=True,
        check=False
    )
    
    if result.returncode == 0:
        print(f"✅ Updated label: {name}")
        return True
    
    # If update failed (label doesn't exist), create it
    if "not found" in result.stderr.lower() or "could not resolve" in result.stderr.lower():
        result = subprocess.run(
            [
                "gh", "label", "create", name,
                "--color", color,
                "--description", description
            ],
            capture_output=True,
            text=True,
            check=False
        )
        
        if result.returncode == 0:
            print(f"✅ Created label: {name}")
            return True
        elif "already exists" in result.stderr.lower():
            print(f"ℹ️  Label already exists: {name}")
            return True
        else:
            print(f"❌ Error creating label '{name}': {result.stderr}")
            return False
    else:
        print(f"❌ Error updating label '{name}': {result.stderr}")
        return False


def main():
    """Main function to create all labels."""
    print("🏷️  GitHub Label Creator for Dependabot and Workflows")
    print("=" * 60)
    
    # Check prerequisites
    if not check_gh_cli():
        sys.exit(1)
    
    print(f"\nCreating {len(LABELS)} labels...\n")
    
    success_count = 0
    error_count = 0
    
    for label in LABELS:
        if create_or_update_label(label):
            success_count += 1
        else:
            error_count += 1
    
    print("\n" + "=" * 60)
    print(f"✅ Successfully processed: {success_count} labels")
    if error_count > 0:
        print(f"❌ Errors: {error_count} labels")
        sys.exit(1)
    else:
        print("\n🎉 All labels created/updated successfully!")


if __name__ == "__main__":
    main()
