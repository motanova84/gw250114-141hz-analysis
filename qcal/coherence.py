def psi_score(text: str) -> float:
    intention_count = text.count("intención") + text.count("propósito") + text.count("coherencia")
    A_eff = len(set(text.split())) / (len(text.split()) + 1e-6)
    return intention_count * A_eff ** 2
