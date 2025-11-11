# llama4_coherence.py
import os
import torch
from transformers import LlamaForCausalLM, LlamaTokenizer

MODEL_ID = "meta-llama/Llama-4-Maverick-17B-128E-Instruct-FP8"
CACHE_DIR = "./models/llama4"


class Llama4Coherence:
    def __init__(self):
        self.tokenizer = LlamaTokenizer.from_pretrained(
            MODEL_ID, cache_dir=CACHE_DIR, use_auth_token=os.getenv("HF_TOKEN")
        )
        self.model = LlamaForCausalLM.from_pretrained(
            MODEL_ID, cache_dir=CACHE_DIR, torch_dtype=torch.float16, device_map="auto"
        )

    def get_coherence_score(self, text: str) -> float:
        """Devuelve Ψ ∈ [0,1] basado en coherencia interna de Llama 4"""
        prompt = f"Rate the logical coherence of this text from 0 to 1 (only return number):\n\n{text}"
        inputs = self.tokenizer(prompt, return_tensors="pt").to(self.model.device)
        with torch.no_grad():
            outputs = self.model.generate(**inputs, max_new_tokens=5, temperature=0.1)
        result = self.tokenizer.decode(outputs[0], skip_special_tokens=True).strip()
        try:
            return float(result)
        except (ValueError, TypeError):
            return 0.5  # fallback
