def kl_divergence(text: str) -> float:
    from collections import Counter
    import math
    words = text.split()
    freqs = Counter(words)
    total = sum(freqs.values())
    probs = [v / total for v in freqs.values()]
    return -sum(p * math.log(p + 1e-9) for p in probs)


def snr(text: str) -> float:
    words = text.split()
    unique = set(words)
    return len(unique) / (len(words) + 1e-6)


def strich_rate(text: str) -> float:
    return text.count("∴") / max(1, len(text))
