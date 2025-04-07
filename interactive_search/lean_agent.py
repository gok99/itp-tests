import streamlit as st
from lean_dojo import *
from queue import Queue
from typing import List, Tuple
from dataclasses import dataclass

# Import your actual model runners
from models.claude_runner import ClaudeRunner
from prompt_templates.separation_logic import template as sl_template
from prompt_templates.suggested_prompt import template as pure_template

def pp_goal(goal: Goal) -> str:
    newline = "\n"
    return f'{newline.join([decl.ident + " : " + decl.lean_type for decl in goal.assumptions])} ⊢ {goal.conclusion}'

def flatten(l):
    return [item for sublist in l for item in sublist]

@dataclass
class ProofState:
    tactics: List[str]
    obligation: str
    result: TacticResult | None

class ProofCoordinator:
    def __init__(self):
        self.working_proofs = Queue()
        self.retry_proofs = Queue()
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
        
        # Streamlit app state
        if 'current_depth' not in st.session_state:
            st.session_state.current_depth = 0
        if 'max_depth' not in st.session_state:
            st.session_state.max_depth = 10
        if 'proof_found' not in st.session_state:
            st.session_state.proof_found = False
        if 'final_proof' not in st.session_state:
            st.session_state.final_proof = []
        if 'proof_log' not in st.session_state:
            st.session_state.proof_log = []
        if 'initialized' not in st.session_state:
            st.session_state.initialized = False
        if 'dojo' not in st.session_state:
            st.session_state.dojo = None
        if 'init_state' not in st.session_state:
            st.session_state.init_state = None
        if 'current_state' not in st.session_state:
            st.session_state.current_state = None
        if 'tactic_suggestions' not in st.session_state:
            st.session_state.tactic_suggestions = []
        if 'proof_history' not in st.session_state:
            st.session_state.proof_history = []
        if 'history_index' not in st.session_state:
            st.session_state.history_index = -1
        if 'user_intuition' not in st.session_state:
            st.session_state.user_intuition = ""

    def process_obligation(self, state: ProofState) -> Tuple[List[ProofState], List[ProofState]]:
        dojo = st.session_state.dojo
        
        valid_next_states = []
        invalid_next_states = []
        
        # Log current state
        st.session_state.proof_log.append(f"Processing goal: {state.obligation}")

        input_text = state.obligation
        print("USER INTUITION", st.session_state.user_intuition)
        if st.session_state.user_intuition.strip():
            input_text += f"\n\nAdditional intuition: {st.session_state.user_intuition}"
            st.session_state.proof_log.append(f"Using additional intuition: {st.session_state.user_intuition}")
            
        print(input_text)

        # Generate tactic suggestions
        suggestions = self.base_runner.generate(input=input_text)
        suggestions = flatten([
            self.pure_runner.generate(input=input_text) 
            if tactic == "PURE" else [(tactic, conf)] 
            for tactic, conf in suggestions
        ])
        suggestions.sort(key=lambda x: x[1], reverse=True)
        
        # Store suggestions for UI
        st.session_state.tactic_suggestions = [(tactic, conf) for tactic, conf in suggestions]
        
        # Log suggestions
        suggestion_log = "\nTactic suggestions:\n"
        for tactic, conf in suggestions:
            suggestion_log += f"- {tactic} (confidence: {conf:.2f})\n"
        st.session_state.proof_log.append(suggestion_log)

        for tactic, _ in suggestions:
            try:
                result = dojo.run_tac(state.result, tactic)
                if isinstance(result, LeanError):
                    obligation = state.obligation + "\n\n" \
                        + f'- {tactic} did not work with error: {result.error}'
                    invalid_next_states.append(
                        ProofState(state.tactics, obligation, state.result))
                    st.session_state.proof_log.append(f"✗ Tactic '{tactic}' failed: {result.error}")
                elif isinstance(result, ProofGivenUp):
                    st.session_state.proof_log.append(f"✗ Tactic '{tactic}' gave up")
                    pass
                else:
                    new_tactics = state.tactics + [tactic]

                    if isinstance(result, ProofFinished):
                        st.session_state.proof_log.append(f"✓ Tactic '{tactic}' completed the proof!")
                        st.session_state.proof_found = True
                        st.session_state.final_proof = new_tactics
                        return ([ProofState(new_tactics, state.obligation, result)], [])
                    elif isinstance(result, TacticResult):
                        tactic_log = f"✓ Applied tactic '{tactic}'"
                        if result.goals:
                            tactic_log += f" - Generated {len(result.goals)} new goals"
                        st.session_state.proof_log.append(tactic_log)
                        
                        for goal in result.goals:
                            goal_text = pp_goal(goal=goal)
                            st.session_state.proof_log.append(f"New goal: {goal_text}")
                            valid_next_states.append(
                                ProofState(new_tactics, goal_text, result))
                    else:
                        st.session_state.proof_log.append(f"! Unexpected result type for tactic '{tactic}'")
                        pass
            except Exception as e:
                st.session_state.proof_log.append(f"! Exception '{e}' encountered running tactic: {tactic}")
                pass
                
        return valid_next_states, invalid_next_states

    def run_manual_tactic(self, tactic: str) -> bool:
        """Run a manually provided tactic and update the proof state"""
        if st.session_state.current_state is None:
            st.session_state.proof_log.append("No current state to apply tactic to.")
            return False
            
        dojo = st.session_state.dojo
        state = st.session_state.current_state
        
        st.session_state.proof_log.append(f"\n=====================================")
        st.session_state.proof_log.append(f"Manually applying tactic: {tactic}")
        st.session_state.current_depth += 1
        
        try:
            result = dojo.run_tac(state.result, tactic)
            
            if isinstance(result, LeanError):
                st.session_state.proof_log.append(f"✗ Tactic '{tactic}' failed: {result.error}")
                return False
            elif isinstance(result, ProofGivenUp):
                st.session_state.proof_log.append(f"✗ Tactic '{tactic}' gave up")
                return False
            else:
                new_tactics = state.tactics + [tactic]

                if isinstance(result, ProofFinished):
                    st.session_state.proof_log.append(f"✓ Tactic '{tactic}' completed the proof!")
                    st.session_state.proof_found = True
                    st.session_state.final_proof = new_tactics
                    return True
                elif isinstance(result, TacticResult):
                    tactic_log = f"✓ Applied tactic '{tactic}'"
                    if result.goals:
                        tactic_log += f" - Generated {len(result.goals)} new goals"
                        
                        # Update the current state to the first new goal
                        goal = result.goals[0]
                        goal_text = pp_goal(goal=goal)
                        st.session_state.current_state = ProofState(new_tactics, goal_text, result)
                        
                        # Add new state to history, truncate any future states
                        if st.session_state.history_index < len(st.session_state.proof_history) - 1:
                            st.session_state.proof_history = st.session_state.proof_history[:st.session_state.history_index + 1]
                        st.session_state.proof_history.append(st.session_state.current_state)
                        st.session_state.history_index = len(st.session_state.proof_history) - 1

                        # Update working queue for auto mode
                        self.working_proofs = Queue()
                        self.working_proofs.put(st.session_state.current_state)
                        
                        # Log all new goals
                        st.session_state.proof_log.append(tactic_log)
                        for i, goal in enumerate(result.goals):
                            goal_text = pp_goal(goal=goal)
                            if i == 0:
                                st.session_state.proof_log.append(f"Current goal: {goal_text}")
                            else:
                                st.session_state.proof_log.append(f"Additional goal {i}: {goal_text}")
                    else:
                        st.session_state.proof_log.append(f"{tactic_log} - No new goals generated")
                                        
                    return True
                else:
                    st.session_state.proof_log.append(f"! Unexpected result state for tactic '{tactic}'")
                    return False
        except Exception as e:
            st.session_state.proof_log.append(f"! Exception '{e}' encountered running tactic: {tactic}")
            return False

    # 4. Add a simpler backtrack method for the slider:
    def backtrack_to_state(self, index: int) -> bool:
        """Backtrack to a previous proof state"""
        if 0 <= index < len(st.session_state.proof_history):
            st.session_state.current_state = st.session_state.proof_history[index]
            st.session_state.history_index = index
            
            # Update working queue for auto mode
            self.working_proofs = Queue()
            self.working_proofs.put(st.session_state.current_state)
            
            # Log the backtrack
            st.session_state.proof_log.append(f"\n=====================================")
            st.session_state.proof_log.append(f"Backtracked to state {index+1}/{len(st.session_state.proof_history)}")
            st.session_state.proof_log.append(f"Current goal: {st.session_state.current_state.obligation}")
            
            return True
        return False

    def initialize_proof(self, repo_url, commit_hash, theorem_file, theorem_name):
        """Initialize the proof process with the given theorem"""
        try:
            # Clear existing state
            st.session_state.proof_log = []
            st.session_state.proof_log.append(f"Initializing proof for theorem: {theorem_name} from {theorem_file}")
            
            # Set up the repository and theorem
            repo = LeanGitRepo(repo_url, commit_hash)
            theorem = Theorem(repo, theorem_file, theorem_name)
            
            # This will create a Dojo instance that we'll reuse
            # Note: This approach keeps the Dojo open during the Streamlit session
            # You might need a different approach if your app needs to be more stateless
            dojo_and_state = Dojo(theorem).__enter__()
            st.session_state.dojo = dojo_and_state[0]
            st.session_state.init_state = dojo_and_state[1]
            
            # Log the initial goal
            initial_goal = st.session_state.init_state.goals[0]
            goal_text = pp_goal(initial_goal)
            st.session_state.proof_log.append(f"Initial goal: {goal_text}")
            
            # Initialize working queue with the first proof state
            self.working_proofs = Queue()
            self.retry_proofs = Queue()
            initial_state = ProofState([], goal_text, st.session_state.init_state)
            self.working_proofs.put(initial_state)
            
            # Store necessary state in session
            st.session_state.current_depth = 0
            st.session_state.proof_found = False
            st.session_state.final_proof = []
            st.session_state.initialized = True
            st.session_state.theorem_file = theorem_file
            st.session_state.theorem_name = theorem_name
            st.session_state.proof_history = []
            st.session_state.history_index = -1
            
            # Store current state for manual mode and generate suggestions
            st.session_state.current_state = initial_state
            st.session_state.proof_history.append(initial_state)
            st.session_state.history_index = 0
            
            return True
            
        except Exception as e:
            st.error(f"Error initializing proof: {e}")
            return False

    def step_proof(self):
        """Perform one step in the proof search process"""
        if st.session_state.proof_found or st.session_state.current_depth >= st.session_state.max_depth:
            return
        
        st.session_state.current_depth += 1
        st.session_state.proof_log.append(f"\n=====================================")
        st.session_state.proof_log.append(f"Starting auto step at depth {st.session_state.current_depth}")
        
        if self.working_proofs.empty():
            if self.retry_proofs.empty():
                st.session_state.proof_log.append("No more proof states to explore.")
                return
            else:
                st.session_state.proof_log.append("Moving retry proofs to working queue.")
                while not self.retry_proofs.empty():
                    self.working_proofs.put(self.retry_proofs.get())

        current_state = self.working_proofs.get()
        st.session_state.current_state = current_state  # Update current state for UI
        
        (valid, invalid) = self.process_obligation(current_state)
        
        st.session_state.proof_log.append("=======")
        st.session_state.proof_log.append(f"Valid tactic applications: {len(valid)}")
        
        # Process valid states
        for state in valid:
            if st.session_state.proof_found:
                return
                
            if isinstance(state.result, ProofFinished):
                st.session_state.proof_found = True
                st.session_state.final_proof = state.tactics
                return

            self.working_proofs.put(state)
            
        # Update current state to the first valid state if available
        if valid:
            st.session_state.current_state = valid[0]

            # Add new state to history, truncate any future states
            if st.session_state.history_index < len(st.session_state.proof_history) - 1:
                st.session_state.proof_history = st.session_state.proof_history[:st.session_state.history_index + 1]
            st.session_state.proof_history.append(st.session_state.current_state)
            st.session_state.history_index = len(st.session_state.proof_history) - 1
            
        # Process invalid states
        for state in invalid:
            self.retry_proofs.put(state)

        st.session_state.proof_log.append(f"Finished auto step at depth {st.session_state.current_depth}")
        st.session_state.proof_log.append(f"Num new proofs: {len(valid)}")
        st.session_state.proof_log.append(f"Num invalid proofs: {len(invalid)}")
        
        return

    def cleanup(self):
        """Clean up Dojo resources when app is closed or restarted"""
        if st.session_state.dojo is not None:
            try:
                # Call __exit__ method of Dojo to clean up resources
                Dojo.__exit__(st.session_state.dojo, None, None, None)
                st.session_state.dojo = None
                st.session_state.init_state = None
            except Exception as e:
                st.error(f"Error cleaning up Dojo: {e}")

def main():
    st.set_page_config(
        page_title="Lean Proof Coordinator",
        page_icon="📝",
        layout="wide"
    )
    
    st.title("Lean Proof Coordinator")
    
    # Initialize the coordinator
    if 'coordinator' not in st.session_state:
        st.session_state.coordinator = ProofCoordinator()
    
    # Setup sidebar
    with st.sidebar:
        st.header("Configuration")
        
        # Theorem selection
        st.subheader("Theorem")
        repo_url = st.text_input("Repository URL:", value="/home/gok99/Local/proof-synthesis/splean")
        commit_hash = st.text_input("Commit hash:", value="463c856194c85ad59ca461bf1097eed24e722ed0")
        theorem_file = st.text_input("Theorem file path:", value="SPLean/Experiments/Misc.lean")
        theorem_name = st.text_input("Theorem name:", value="Lang.array_exists_spec")
        
        # Proof parameters
        st.subheader("Parameters")
        max_depth = st.slider("Maximum search depth:", min_value=1, max_value=50, value=10)
        st.session_state.max_depth = max_depth
        
        # Initialize button
        if st.button("Initialize Proof Search", type="primary"):
            st.session_state.coordinator.initialize_proof(repo_url, commit_hash, theorem_file, theorem_name)
            st.rerun()

    # Main content area - use 3 columns layout
    col1, col2, col3 = st.columns([2, 4, 2])
    
    with col1:
        st.header("Proof Progress")
        
        # Display proof log
        if 'proof_log' in st.session_state:
            log_text = "\n".join(st.session_state.proof_log)
            st.text_area("Log:", value=log_text, height=400, disabled=True)
    
    with col2:
        st.header("Current Goal")
        
        if st.session_state.get('initialized', False) and not st.session_state.get('proof_found', False):
            if len(st.session_state.proof_history) > 1:
                st.markdown("### Proof History")
                
                # Display a slider to navigate through states
                history_length = len(st.session_state.proof_history)
                slider_val = st.slider(
                    "Navigate through proof states", 
                    min_value=0, 
                    max_value=history_length-1, 
                    value=st.session_state.history_index,
                    key="history_slider"
                )
                
                # Check if slider value changed
                if slider_val != st.session_state.history_index:
                    st.session_state.coordinator.backtrack_to_state(slider_val)
                    st.rerun()
                
                # Show current position info
                st.info(f"Current state: {slider_val+1}/{history_length}")

            # Show current goal
            if st.session_state.current_state:
                st.code(st.session_state.current_state.obligation, language="lean")
            
            # Add intuition input textbox
            st.markdown("### Additional Intuition")
            intuition = st.text_area(
                "Input any additional intuition or hints to guide the proof:",
                value=st.session_state.get('user_intuition', ""),
                height=100,
                key="intuition_input"
            )
            # Store the intuition in session state
            st.session_state.user_intuition = intuition

            # Auto step button
            if st.button("Take Auto Step", type="primary"):
                st.session_state.coordinator.step_proof()
                st.session_state.user_intuition = ""
                st.rerun()
                
            # Manual tactic input
            st.markdown("### Manual Tactic")
            manual_tactic = st.text_input("Enter tactic:", key="manual_tactic")
            
            # Apply manual tactic button
            if st.button("Apply Manual Tactic") and manual_tactic:
                st.session_state.coordinator.run_manual_tactic(manual_tactic)
                st.rerun()
    
    with col3:
        st.header("Proof Status")
        
        # Display current status
        if st.session_state.get('initialized', False):
            st.subheader(f"Theorem: {st.session_state.get('theorem_name', '')}")
            st.write(f"Current depth: {st.session_state.current_depth}/{st.session_state.max_depth}")
            
            progress = min(1.0, st.session_state.current_depth / st.session_state.max_depth)
            st.progress(progress)

            if not st.session_state.get('proof_found', False) and len(st.session_state.proof_history) > 1:
                # Display tactics that led to current state
                if slider_val > 0:
                    previous_tactics = st.session_state.proof_history[slider_val].tactics
                    if previous_tactics:
                        st.markdown("#### Tactics applied so far:")
                        tactic_text = "\n".join(previous_tactics)
                        st.code(tactic_text, language="lean")
            
            # Show suggested tactics
            if not st.session_state.get('proof_found', False):
                st.subheader("Suggested Tactics")
                for i, (tactic, conf) in enumerate(st.session_state.tactic_suggestions[:5]):
                    col_a, col_b = st.columns([4, 1])
                    with col_a:
                        st.code(tactic, language="lean")
                    with col_b:
                        if st.button("Apply", key=f"apply_{i}"):
                            st.session_state.coordinator.run_manual_tactic(tactic)
                            st.rerun()
            
            # Show proof status
            if st.session_state.get('proof_found', False):
                st.success("✓ Proof found!")
                st.subheader("Final proof:")
                # for i, tactic in enumerate(st.session_state.final_proof):
                # st.code(f"{tactic}", language="lean")
                st.code("\n".join(st.session_state.final_proof), language="lean")
                st.session_state.coordinator.cleanup()
            elif st.session_state.current_depth >= st.session_state.max_depth:
                st.error("× Reached maximum depth without finding a proof")
            else:
                st.info("🔍 Searching for proof...")
        else:
            st.info("Initialize a proof search to begin")

if __name__ == "__main__":
    main()