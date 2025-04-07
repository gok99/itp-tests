from lean_dojo import *

def pp_goal(goal: Goal) -> str:
    newline = "\n"
    return f'{newline.join([decl.ident + " : " + decl.lean_type for decl in goal.assumptions])} ⊢ {goal.conclusion}'

def flatten(l):
    return [item for sublist in l for item in sublist]

from typing import List, Tuple
from dataclasses import dataclass

from queue import Queue

from models.claude_runner import ClaudeRunner
from prompt_templates.separation_logic import template as sl_template
from prompt_templates.suggested_prompt import template as pure_template

@dataclass
class ProofState:
    tactics: List[str]
    obligation: str
    result: TacticResult | None

# Pure goal tool
# "name": "PureGoalProver",
# "description": "A tool that can prove pure goals that do not contain any domain specific triples.",
# "input_schema": {
#     "type": "object",
#     "properties": {},
#     "required": []
# }

class ProofCoordinator:
    def __init__(self, interactive: bool = False):
        self.working_proofs: Queue[ProofState] = Queue()
        self.retry_proofs: Queue[ProofState] = Queue()
        self.interactive = interactive
        self.base_runner = ClaudeRunner(
            model="claude-3-5-haiku-latest",
            max_tokens=100,
            template=sl_template
        )
        self.pure_runner = ClaudeRunner(
            model="claude-3-5-haiku-latest",
            max_tokens=100,
            template=pure_template
        )

    def process_obligation(self, dojo: Dojo, state: ProofState) -> Tuple[List[ProofState], List[ProofState]]:
        valid_next_states = []
        invalid_next_states = []
        suggestions = self.base_runner.generate(input=state.obligation)
        suggestions = flatten([
            self.pure_runner.generate(input=state.obligation) 
            if tactic == "PURE" else [(tactic, conf)] 
            for tactic, conf in suggestions
        ])
        suggestions.sort(key=lambda x: x[1], reverse=True)

        for tactic, _ in suggestions:
            try:
                result = dojo.run_tac(state.result, tactic)
                if isinstance(result, LeanError):
                    obligation = state.obligation + "\n\n" \
                        + f'- {tactic} did not work with error: {result.error}'
                    invalid_next_states.append(
                        ProofState(state.tactics, obligation, state.result))
                elif isinstance(result, ProofGivenUp):
                    # not sure what to do, just skip
                    pass
                else:
                    new_tactics = state.tactics + [tactic]

                    if isinstance(result, ProofFinished):
                        return ([ProofState(new_tactics, state.obligation, result)], [])
                    elif isinstance(result, TacticResult):
                        for goal in result.goals:
                            valid_next_states.append(
                                ProofState(new_tactics, 
                                           pp_goal(goal=goal),  
                                           result))
                    else:
                        # should never happen
                        print("Unexpected result type", result)
                        pass
            except Exception as e:
                print(f'Exception {e} encountered running tactic: {tactic}')
                pass
                
        return valid_next_states, invalid_next_states

    def prove(self, theorem: Theorem, max_depth: int = 10) -> List[str]:
        with Dojo(theorem) as (dojo, init_state):
            # assume only one goal
            print(f"Initial goal: {init_state.goals[0]}")
            self.working_proofs.put(ProofState([], pp_goal(init_state.goals[0]), init_state))
            
            if self.interactive:
                print("Start proof search? Press any key to start...")
                input()

            for i in range(max_depth):
                if self.working_proofs.empty():
                    if self.retry_proofs.empty():
                        break
                    else:
                        while not self.retry_proofs.empty():
                            self.working_proofs.put(self.retry_proofs.get())

                current_state = self.working_proofs.get()

                print("=====================================")

                if self.interactive:
                    print(f"Processing proof state: {current_state.obligation}")

                (valid, invalid) = self.process_obligation(dojo, current_state)
                
                if self.interactive:
                    print("=======")
                    print(f"Valid tactic applications: {len(valid)}\n\n")

                for state in valid:
                    if self.interactive:
                        print(f'Applied tactic {state.tactics[-1]} to get: {state.result}')
                        print(f'New goal: {state.obligation}')
                        print()
                    if isinstance(state.result, ProofFinished):
                        return state.tactics

                    self.working_proofs.put(state)

                for state in invalid:
                    self.retry_proofs.put(state)

                print(f"Finished depth {i}")
                print(f"Num new proofs: {len(valid)}")
                print(f"Num invalid proofs: {len(invalid)}")

                if self.interactive:
                    print("Press any key to continue to next iteration...")
                    input()
                       
        return []  # Return empty list if no proof found

# Example usage:

repo = LeanGitRepo("/home/gok99/Local/proof-synthesis/splean", "463c856194c85ad59ca461bf1097eed24e722ed0")
theorem = Theorem(repo, "SPLean/Experiments/Misc.lean", "Lang.add_pointer_spec")
# trace(repo, dst_dir="traced_splean")

# repo = LeanGitRepo("/home/gok99/logical_verification_2023", "538998ad7545c066bb5e4a3312cb59be225b06ca")
# theorem = Theorem(repo, "LoVe/LoVe03_BackwardProofs_ExerciseSheet.lean", "LoVe.BackwardProofs.SorryTheorems.EM_of_DN")

# repo = LeanGitRepo("https://github.com/yangky11/lean4-example", "7b6ecb9ad4829e4e73600a3329baeb3b5df8d23f")
# theorem = Theorem(repo, "Lean4Example.lean", "hello_world")

coordinator = ProofCoordinator(interactive=True)
proof = coordinator.prove(theorem)
print("Found proof:", proof)
