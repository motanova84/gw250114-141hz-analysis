# QCAL-LLM Quick Start Guide

Get QCAL-LLM running in under 5 minutes.

## Prerequisites

- Docker installed with GPU support (for CUDA acceleration)
- OR Python 3.11+ with pip

## Option 1: Docker (Recommended)

### Pull and Run

```bash
# Pull the pre-built image
docker pull motanova/qcal-llm:latest-gpu

# Run the API server
docker run --gpus all -p 8000:8000 motanova/qcal-llm:latest-gpu

# Test the endpoint
curl http://localhost:8000/
```

### Use the API

```bash
# Send a test request
curl http://localhost:8000/v1/chat/completions \
  -H "Content-Type: application/json" \
  -d @examples/gsm8k_qcal.json
```

### Custom Configuration

```bash
docker run --gpus all -p 8000:8000 \
  -e MODEL=llama-4-70b \
  -e QCAL_FREQUENCY=141.7001 \
  -e QCAL_EPSILON=0.015 \
  motanova/qcal-llm:latest-gpu
```

## Option 2: Local Python

### Install Dependencies

```bash
# Clone the repository
git clone https://github.com/motanova84/141hz.git
cd 141hz/QCAL-LLM

# Install requirements
pip install -r requirements.txt
```

### Run Benchmarks

```bash
# Run single benchmark
python benchmarks/run_gsm8k.py --model llama-4-405b --qcal-mode

# Run all benchmarks via Makefile
make benchmark MODEL=llama-4-405b
```

## Option 3: Integration with Existing Code

### Python Integration

```python
import json
import math

def apply_qcal_modulation(text: str, frequency: float = 141.7001, 
                          epsilon: float = 0.015, tau: float = 0.07) -> str:
    """Apply QCAL 141.7 Hz modulation to input text"""
    lines = text.split('\n')
    modulated = []
    
    for i, line in enumerate(lines):
        if line.strip():
            t = i / frequency
            mod = 1.0 + epsilon * math.cos(2 * math.pi * frequency * t) * math.exp(-t / tau)
            
            # Apply subtle spacing
            if mod > 1.0:
                spaces = int(mod * 10) % 3
                line = line + ' ' * spaces
        
        modulated.append(line)
    
    return '\n'.join(modulated)

# Use with any LLM
user_prompt = "Explain quantum entanglement"
modulated_prompt = apply_qcal_modulation(user_prompt)

# Send to your model
# response = your_model.generate(modulated_prompt)
```

### OpenAI API Compatible

```python
import openai

# Point to QCAL-LLM server
client = openai.OpenAI(
    base_url="http://localhost:8000/v1",
    api_key="not-needed"
)

# Use exactly like OpenAI API
response = client.chat.completions.create(
    model="llama-4-405b-qcal",
    messages=[
        {"role": "system", "content": "You are a helpful assistant."},
        {"role": "user", "content": "What is the meaning of life?"}
    ],
    extra_body={
        "qcal_frequency": 141.7001,
        "qcal_enabled": True
    }
)

print(response.choices[0].message.content)
```

## Verify Installation

### Test Suite

```bash
# Run all tests
make test

# Or manually
python -m pytest ../test_qcal_llm.py -v
```

### Health Check

```bash
# Docker health check
docker ps --filter "name=qcal-llm" --format "{{.Status}}"

# API health check
curl http://localhost:8000/health
```

## Common Issues

### GPU Not Detected

**Problem:** Docker can't access GPU

**Solution:**
```bash
# Install nvidia-docker
sudo apt-get install -y nvidia-docker2
sudo systemctl restart docker

# Verify GPU access
docker run --rm --gpus all nvidia/cuda:12.4.0-base-ubuntu22.04 nvidia-smi
```

### Port Already in Use

**Problem:** Port 8000 is already taken

**Solution:**
```bash
# Use a different port
docker run --gpus all -p 8080:8000 motanova/qcal-llm:latest-gpu

# Update API calls
curl http://localhost:8080/v1/chat/completions ...
```

### Out of Memory

**Problem:** Model too large for available GPU memory

**Solution:**
```bash
# Use a smaller model
docker run --gpus all -p 8000:8000 \
  -e MODEL=llama-4-70b \
  motanova/qcal-llm:latest-gpu

# Or use quantization
docker run --gpus all -p 8000:8000 \
  -e MODEL=llama-4-405b \
  -e QUANTIZATION=int4 \
  motanova/qcal-llm:latest-gpu
```

## Next Steps

1. **Run Your First Benchmark**
   ```bash
   make benchmark MODEL=your-model-name
   ```

2. **Compare QCAL vs Baseline**
   ```bash
   # Baseline
   python benchmarks/run_gsm8k.py --model llama-4-405b
   
   # With QCAL
   python benchmarks/run_gsm8k.py --model llama-4-405b --qcal-mode
   ```

3. **Explore the Leaderboard**
   
   Visit: http://141hz.org/leaderboard

4. **Read the Full Documentation**
   
   See: [README.md](README.md)

## Getting Help

- **Issues:** https://github.com/motanova84/141hz/issues
- **Discussions:** https://github.com/motanova84/141hz/discussions
- **Twitter:** [@motanova84](https://twitter.com/motanova84)

## License

MIT License - See [LICENSE](../LICENSE)

---

**Ready to reduce hallucinations? Start now!** 🚀
