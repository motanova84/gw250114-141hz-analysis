"""Test suite for LLaMA 4 setup and integration."""
import os
from pathlib import Path


def test_setup_script_exists():
    """Test that setup script exists and is executable."""
    script_path = Path("scripts/setup_llama4.sh")
    assert script_path.exists(), "setup_llama4.sh should exist"
    assert os.access(script_path, os.X_OK), "setup_llama4.sh should be executable"


def test_setup_script_content():
    """Test that setup script has expected commands."""
    script_path = Path("scripts/setup_llama4.sh")
    content = script_path.read_text()

    assert "#!/bin/bash" in content, "Should have bash shebang"
    assert "mkdir -p models/llama4/weights" in content, "Should create directories"
    assert "curl" in content, "Should use curl for download"
    assert "tar -xzvf" in content, "Should extract tarball"
    assert "LLAMA4_SIGNED_URL" in content, "Should use LLAMA4_SIGNED_URL env var"


def test_prompts_json_exists():
    """Test that prompts JSON file exists."""
    prompts_path = Path("data/prompts_qcal.json")
    assert prompts_path.exists(), "prompts_qcal.json should exist"


def test_qcal_module_exists():
    """Test that qcal module exists with required files."""
    qcal_path = Path("qcal")
    assert qcal_path.exists(), "qcal directory should exist"
    assert (qcal_path / "__init__.py").exists(), "__init__.py should exist"
    assert (qcal_path / "coherence.py").exists(), "coherence.py should exist"
    assert (qcal_path / "metrics.py").exists(), "metrics.py should exist"


def test_llama4_coherence_exists():
    """Test that llama4_coherence.py exists."""
    coherence_path = Path("llama4_coherence.py")
    assert coherence_path.exists(), "llama4_coherence.py should exist"


def test_qcal_llm_eval_exists():
    """Test that qcal_llm_eval.py exists."""
    eval_path = Path("scripts/qcal_llm_eval.py")
    assert eval_path.exists(), "qcal_llm_eval.py should exist"


def test_benchmark_notebook_exists():
    """Test that benchmark notebook exists."""
    notebook_path = Path("notebooks/benchmark_llama4.ipynb")
    assert notebook_path.exists(), "benchmark_llama4.ipynb should exist"


def test_qcal_baliza_exists():
    """Test that .qcal_baliza marker exists."""
    baliza_path = Path(".qcal_baliza")
    assert baliza_path.exists(), ".qcal_baliza should exist"

    content = baliza_path.read_text()
    assert "DO NOT DELETE" in content, "Should have DO NOT DELETE warning"
    assert "141.7001 Hz" in content, "Should reference f₀"


if __name__ == "__main__":
    print("Running LLaMA 4 integration tests...")

    test_setup_script_exists()
    print("✓ test_setup_script_exists passed")

    test_setup_script_content()
    print("✓ test_setup_script_content passed")

    test_prompts_json_exists()
    print("✓ test_prompts_json_exists passed")

    test_qcal_module_exists()
    print("✓ test_qcal_module_exists passed")

    test_llama4_coherence_exists()
    print("✓ test_llama4_coherence_exists passed")

    test_qcal_llm_eval_exists()
    print("✓ test_qcal_llm_eval_exists passed")

    test_benchmark_notebook_exists()
    print("✓ test_benchmark_notebook_exists passed")

    test_qcal_baliza_exists()
    print("✓ test_qcal_baliza_exists passed")

    print("\n✅ All integration tests passed!")
