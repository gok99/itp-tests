from typing import List, Tuple
import os

try:
    from anthropic import Anthropic
except ImportError as e:
    pass
from .external_parser import *


class ClaudeRunner(Generator, Transformer):
    client = Anthropic(api_key=os.getenv("ANTHROPIC_KEY"))

    def __init__(self, **args):
        self.client_kwargs = {
            "model": args["model"],
            "max_tokens": args["max_tokens"],
        }
        self.template = args["template"]
        self.name = self.client_kwargs["model"]

    def generate(self, input: str, target_prefix: str = "") -> List[Tuple[str, float]]:
        (system, message) = self.template(input)

        print(system)
        print(message)
        response = self.client.messages.create(
            system=[
                {
                    "type": "text",
                    "text": system,
                    "cache_control": {"type": "ephemeral"}
                }
            ],
            messages=[{
                "role": "user",
                "content": message,
            }],
            **self.client_kwargs,
        )
        print(response)
        content = response.content[0].text
        result = content.split("<tactic>")[-1].split("</tactic>")[0]

        results = [
            (result, 1.0)
        ]  # Currently Claude only supports one output.
        return choices_dedup(results)

if __name__ == "__main__":
    generation_kwargs = {
        "model": "claude-3-5-haiku-20241022",
        "max_tokens": 100,
        "template": lambda obligation: ("", f"""
            Suggest a tactic to address the following proof obligation:
            {obligation}
            """)
    }

    model = ClaudeRunner(**generation_kwargs)
    print(model.generate("n : ℕ\n⊢ gcd n n = n"))
