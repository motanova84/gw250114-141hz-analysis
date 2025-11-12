# Security Policy

## Reporting Security Issues

If you discover a security vulnerability in this project, please report it by:

1. **Email**: institutoconsciencia@proton.me (response time: 7 days)
2. **GitHub Security Advisory**: Use the [private reporting feature](https://github.com/motanova84/141hz/security/advisories/new)

**Response Time Objective**: 7 days for initial response to vulnerability reports.

Please do NOT report security vulnerabilities through public GitHub issues.

## Dependency Security

This project uses automated dependency scanning to identify and address security vulnerabilities in dependencies.

### Automated Scanning

The project runs weekly dependency health checks using:
- **pip-audit**: Scans for known security vulnerabilities in Python dependencies
- **GitHub Dependabot**: Monitors for security updates (if enabled)

### Workflow

1. The `dependency-health.yml` workflow runs weekly on Wednesdays at 10:00 UTC
2. It scans all dependencies listed in `requirements.txt`
3. If vulnerabilities are found, an issue is automatically created with:
   - Details of vulnerable packages
   - Affected versions
   - Available fixes
   - Links to security advisories
4. The workflow automatically closes false-positive issues when no real vulnerabilities exist

### Manual Security Checks

You can manually trigger a security check:

```bash
# Install pip-audit
pip install pip-audit

# Run security scan
pip-audit --desc --format json

# Or with requirements file
pip-audit -r requirements.txt
```

## Supported Versions

We support the following Python versions:
- Python 3.11 (production standard)
- Python 3.12 (future-proofing)

## Security Best Practices

### For Contributors

When contributing to this project:

1. **Keep dependencies updated**: Regularly check for security updates
2. **Review security advisories**: Check the [GitHub Advisory Database](https://github.com/advisories)
3. **Follow secure coding practices**: 
   - Validate user inputs
   - Use parameterized queries
   - Avoid hardcoded credentials
   - Use secure random number generators
4. **Test security updates**: Run the full test suite after updating dependencies

### For Maintainers

1. **Monitor security issues**: Check automated security issues regularly
2. **Update promptly**: Apply security patches as soon as possible
3. **Verify compatibility**: Test updates with Python 3.11 and 3.12
4. **Document changes**: Update CHANGELOG.md with security fixes
5. **Communicate**: Notify users of critical security updates

## Recent Security Improvements

### 2025-10-26: Fixed Dependency Health Workflow

**Issue**: The dependency health workflow was creating false-positive security issues even when no vulnerabilities existed.

**Root Cause**: The workflow checked if the pip-audit JSON report file existed, but didn't verify if any packages actually had vulnerabilities. pip-audit generates a report file even when all packages are secure (with empty `vulns` arrays).

**Fix**: 
- Added proper JSON parsing to check if any package has non-empty `vulns` array
- Enhanced issue creation to include detailed vulnerability summaries
- Added automatic closing of false-positive issues
- Improved reporting to clearly distinguish between packages with and without vulnerabilities

**Impact**: Reduces noise from false-positive security alerts and provides more actionable information when real vulnerabilities are detected.

## Security Response Timeline

- **Critical vulnerabilities**: Fix within 24-48 hours
- **High severity**: Fix within 7 days
- **Medium severity**: Fix within 30 days
- **Low severity**: Fix in next regular update cycle

## Disclosure Policy

When we address a security vulnerability:

1. We will acknowledge receipt of the report within 48 hours
2. We will provide an estimated timeline for a fix
3. We will release a patch and security advisory
4. We will credit the reporter (unless anonymity is requested)

## Additional Resources

- [Python Security Best Practices](https://python.readthedocs.io/en/stable/library/security_warnings.html)
- [OWASP Top 10](https://owasp.org/www-project-top-ten/)
- [GitHub Security Features](https://docs.github.com/en/code-security)
- [pip-audit Documentation](https://github.com/pypa/pip-audit)

---

Last updated: 2025-10-26
