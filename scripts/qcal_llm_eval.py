from qcal.coherence import psi_score
from qcal.metrics import kl_divergence, snr, strich_rate
from transformers import AutoTokenizer, AutoModelForCausalLM
import torch
import json


MODEL_PATH = "models/llama4/weights/"
PROMPTS_PATH = "data/prompts_qcal.json"


device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
model = AutoModelForCausalLM.from_pretrained(MODEL_PATH, device_map="auto")
tokenizer = AutoTokenizer.from_pretrained(MODEL_PATH)


with open(PROMPTS_PATH) as f:
    prompts = json.load(f)


results = []


for p in prompts:
    input_ids = tokenizer(p["text"], return_tensors="pt").input_ids.to(device)
    output = model.generate(input_ids, max_new_tokens=100)
    decoded = tokenizer.decode(output[0], skip_special_tokens=True)

    psi = psi_score(decoded)
    snr_val = snr(decoded)
    kld = kl_divergence(decoded)
    strich = strich_rate(decoded)

    results.append({
        "prompt": p["label"],
        "output": decoded,
        "psi": psi,
        "snr": snr_val,
        "kld": kld,
        "strich_rate": strich
    })

    print(f"\n🔹 Prompt: {p['label']}")
    print(f"Ψ = {psi:.3f} | SNR = {snr_val:.2f} | KLD⁻¹ = {1/kld:.2f} | ∴ = {strich:.3f}")
    print(f"Output: {decoded}")


with open("results_llama4.json", "w") as f:
    json.dump(results, f, indent=2)
