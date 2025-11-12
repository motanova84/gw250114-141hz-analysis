#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

# Handle package naming conflict
if [ -d "../../qcal" ] && [ ! -d "../../qcal_backup" ]; then
    echo "Temporarily renaming root qcal/ to avoid conflicts..."
    mv ../../qcal ../../qcal_backup
    RESTORE_QCAL=1
else
    RESTORE_QCAL=0
fi

# Run make commands
make env
make run

# Restore original qcal directory
if [ "$RESTORE_QCAL" -eq 1 ] && [ -d "../../qcal_backup" ]; then
    echo "Restoring root qcal/ directory..."
    mv ../../qcal_backup ../../qcal
fi

echo "Reproducibility run completed!"

