import torch
import numpy as np
from typing import List, Tuple
from abc import ABC, abstractmethod

def get_cuda_if_available():
    return torch.device("cuda" if torch.cuda.is_available() else "cpu")

def find_first_tactic(code: List[str]):
    for s in code:
        ss = s.strip()
        if not ("theorem" in ss or ss.startswith("--") or ss == "" or ":= by" in ss):
            return ss

def choices_dedup(output_list: List[tuple[str, float]]) -> List[tuple[str, float]]:
    unique_data = {}
    for item in output_list:
        if item[0] not in unique_data or item[1] > unique_data[item[0]]:
            unique_data[item[0]] = item[1]
    sorted_data = sorted(unique_data.items(), key=lambda x: x[1], reverse=True)
    return sorted_data


class Generator(ABC):
    @abstractmethod
    def generate(self, input: str, target_prefix: str = "") -> List[Tuple[str, float]]:
        pass


class Encoder(ABC):
    @abstractmethod
    def encode(self, input: str) -> np.ndarray:
        pass


class Transformer:
    def cuda(self) -> None:
        self.model.cuda()

    def cpu(self) -> None:
        self.model.cpu()

    @property
    def device(self) -> torch.device:
        return self.model.device
