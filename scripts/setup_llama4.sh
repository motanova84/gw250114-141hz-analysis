#!/bin/bash
mkdir -p models/llama4/weights
curl -L "$LLAMA4_SIGNED_URL" -o models/llama4/weights/model.tar.gz
tar -xzvf models/llama4/weights/model.tar.gz -C models/llama4/weights/
echo "✅ LLaMA 4 setup complete."
