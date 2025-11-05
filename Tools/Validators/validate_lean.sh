#!/bin/bash
# Validate Lean 4 formalization

set -e

echo "==================================="
echo "Lean 4 Validation"
echo "==================================="

cd "$(dirname "$0")/../../Core"

echo "Checking if lake is installed..."
if ! command -v lake &> /dev/null; then
    echo "❌ Lake (Lean 4 build tool) not found"
    echo "   Install from: https://leanprover.github.io/"
    exit 1
fi

echo "✅ Lake found"
echo ""

echo "Building Lean 4 project..."
lake build

echo ""
echo "✅ Lean 4 validation successful!"
echo "   All proofs compile and verify"
