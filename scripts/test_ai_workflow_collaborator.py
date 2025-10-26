#!/usr/bin/env python3
"""
Test suite for AI Workflow Collaborator
Validates that the health checker and fixer work correctly.
"""

import sys
import os
import yaml
from pathlib import Path

# Add scripts directory to path
sys.path.insert(0, str(Path(__file__).parent))

def test_health_checker_imports():
    """Test that health checker can be imported"""
    try:
        from ai_workflow_health_checker import WorkflowHealthChecker
        print("✅ Health checker imports successfully")
        return True
    except ImportError as e:
        print(f"❌ Failed to import health checker: {e}")
        return False

def test_fixer_imports():
    """Test that fixer can be imported"""
    try:
        from ai_workflow_fixer import WorkflowFixer
        print("✅ Fixer imports successfully")
        return True
    except ImportError as e:
        print(f"❌ Failed to import fixer: {e}")
        return False

def test_health_checker_execution():
    """Test that health checker executes without errors"""
    try:
        from ai_workflow_health_checker import WorkflowHealthChecker
        
        repo_root = Path(__file__).parent.parent
        checker = WorkflowHealthChecker(repo_root)
        results = checker.check_all_workflows()
        
        # Validate results structure
        assert "total_workflows" in results, "Missing total_workflows in results"
        assert "healthy_workflows" in results, "Missing healthy_workflows in results"
        assert "workflows_with_issues" in results, "Missing workflows_with_issues in results"
        assert "issues" in results, "Missing issues in results"
        assert "warnings" in results, "Missing warnings in results"
        assert "recommendations" in results, "Missing recommendations in results"
        
        # Validate results values
        assert results["total_workflows"] > 0, "No workflows found"
        assert results["healthy_workflows"] >= 0, "Invalid healthy_workflows count"
        assert results["workflows_with_issues"] >= 0, "Invalid workflows_with_issues count"
        
        print(f"✅ Health checker executed successfully")
        print(f"   - Analyzed: {results['total_workflows']} workflows")
        print(f"   - Healthy: {results['healthy_workflows']} workflows")
        print(f"   - With issues: {results['workflows_with_issues']} workflows")
        
        return True
    except Exception as e:
        print(f"❌ Health checker execution failed: {e}")
        import traceback
        traceback.print_exc()
        return False

def test_workflow_file_exists():
    """Test that the AI workflow file exists and is valid"""
    try:
        workflow_file = Path(__file__).parent.parent / ".github" / "workflows" / "ai-workflow-collaborator.yml"
        
        if not workflow_file.exists():
            print(f"❌ Workflow file not found: {workflow_file}")
            return False
        
        with open(workflow_file, 'r', encoding='utf-8') as f:
            workflow = yaml.safe_load(f)
        
        # Validate workflow structure
        # Note: YAML parses 'on' as boolean True, so we check for both
        assert workflow is not None, "Workflow is empty"
        assert True in workflow or 'on' in workflow, "Missing 'on' trigger configuration"
        assert 'jobs' in workflow, "Missing 'jobs' section"
        
        jobs = workflow['jobs']
        assert len(jobs) > 0, "No jobs defined"
        
        print(f"✅ Workflow file is valid")
        print(f"   - Name: {workflow.get('name', 'N/A')}")
        print(f"   - Jobs: {list(jobs.keys())}")
        
        return True
    except Exception as e:
        print(f"❌ Workflow validation failed: {e}")
        import traceback
        traceback.print_exc()
        return False

def test_documentation_exists():
    """Test that documentation files exist"""
    repo_root = Path(__file__).parent.parent
    
    docs = {
        "AI_WORKFLOW_COLLABORATOR.md": "Main documentation",
        "QUICKSTART_AI_COLLABORATOR.md": "Quick start guide",
        "AUTOMATED_COLLABORATORS.md": "All collaborators"
    }
    
    all_exist = True
    for doc_file, description in docs.items():
        doc_path = repo_root / doc_file
        if doc_path.exists():
            size = doc_path.stat().st_size
            print(f"✅ {doc_file} exists ({size} bytes) - {description}")
        else:
            print(f"❌ {doc_file} not found - {description}")
            all_exist = False
    
    return all_exist

def main():
    """Run all tests"""
    print("=" * 70)
    print("AI WORKFLOW COLLABORATOR - Test Suite")
    print("=" * 70)
    print()
    
    tests = [
        ("Import Health Checker", test_health_checker_imports),
        ("Import Fixer", test_fixer_imports),
        ("Execute Health Checker", test_health_checker_execution),
        ("Validate Workflow File", test_workflow_file_exists),
        ("Check Documentation", test_documentation_exists),
    ]
    
    results = []
    for test_name, test_func in tests:
        print(f"\n{'='*70}")
        print(f"TEST: {test_name}")
        print(f"{'='*70}")
        success = test_func()
        results.append((test_name, success))
    
    # Summary
    print(f"\n{'='*70}")
    print("TEST SUMMARY")
    print(f"{'='*70}")
    
    passed = sum(1 for _, success in results if success)
    total = len(results)
    
    for test_name, success in results:
        status = "✅ PASSED" if success else "❌ FAILED"
        print(f"  {status:12s} - {test_name}")
    
    print(f"\nTotal: {passed}/{total} tests passed ({100*passed/total:.1f}%)")
    
    if passed == total:
        print("\n🎉 ALL TESTS PASSED!")
        print("✅ AI Workflow Collaborator is ready to use")
        return 0
    else:
        print(f"\n❌ {total - passed} test(s) failed")
        return 1

if __name__ == '__main__':
    sys.exit(main())
