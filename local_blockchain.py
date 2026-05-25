import json
import hashlib
from time import time
import os
from datetime import datetime

# Directory where individual chains (one per activity) will be stored
BLOCKCHAIN_DIR = 'blockchain_data'

class Blockchain:
    def __init__(self, identifier):
        """Initializes a specific blockchain, loading it from file or creating genesis block."""
        self.identifier = identifier
        # Create a unique file path for this specific activity's chain
        self.chain_file = os.path.join(BLOCKCHAIN_DIR, f'chain_{self.identifier}.json')
        self.pending_logs = []
        
        # Create directory if it doesn't exist
        os.makedirs(BLOCKCHAIN_DIR, exist_ok=True)

        self.chain = self.load_chain()
        
        if not self.chain:
            # If the file doesn't exist, create the genesis block
            print(f"--- Creating Genesis Block for Activity ID: {self.identifier} ---")
            self.create_genesis_block()

    def load_chain(self):
        """Loads the chain from its dedicated file."""
        if os.path.exists(self.chain_file):
            try:
                with open(self.chain_file, 'r') as f:
                    return json.load(f)
            except json.JSONDecodeError:
                print(f"Warning: Chain file {self.chain_file} is corrupted or empty.")
                return []
        return []

    def save_chain(self):
        """Saves the current chain to its dedicated file."""
        with open(self.chain_file, 'w') as f:
            json.dump(self.chain, f, indent=4)
        
    def create_genesis_block(self):
        """Creates the first block in the chain."""
        # Arbitrarily set the first block's proof and previous hash
        self.new_block(proof=100, previous_hash='1') 

    # --- CORE BLOCKCHAIN METHODS ---

    def new_block(self, proof, previous_hash=None):
        """
        Mines a new block and adds it to the chain.
        """
        block = {
            'index': len(self.chain) + 1,
            'timestamp': time(),
            # Add all pending logs to the new block
            'logs': self.pending_logs, 
            'proof': proof,
            # Use the hash of the last block, or the provided '1' for genesis block
            'previous_hash': previous_hash or self.hash(self.chain[-1]),
        }
        
        # Reset the current list of logs
        self.pending_logs = []
        
        # Add the new block to the chain and save it
        self.chain.append(block)
        self.save_chain() # CRITICAL: Saves the chain after mining
        return block
    
    def new_log(self, sender, recipient, event_type, details):
        """
        Adds a new transaction/log to the list of pending logs.
        """
        self.pending_logs.append({
            'sender': sender,
            'recipient': recipient,
            'event_type': event_type,
            'details': details,
            'log_timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        })
        # Returns the index of the block that will contain this log
        return self.last_block['index'] + 1

    @staticmethod
    def hash(block):
        """
        Creates a SHA-256 hash of a Block.
        """
        # We must ensure the Dictionary is Ordered, or we'll have inconsistent hashes
        block_string = json.dumps(block, sort_keys=True).encode()
        return hashlib.sha256(block_string).hexdigest()

    @property
    def last_block(self):
        """Returns the last block in the chain."""
        # Ensure a list exists before trying to access elements
        if self.chain:
            return self.chain[-1]
        # Return a dummy block if the chain is empty (shouldn't happen after init)
        return {'index': 0, 'proof': 0, 'previous_hash': '0'}
    
    # --- PROOF OF WORK METHODS ---
    
    def proof_of_work(self, last_proof):
        """
        Simple Proof-of-Work algorithm:
         - Find a number 'p' such that hash(last_proof, p) contains 4 leading zeros.
        """
        proof = 0
        while self.valid_proof(last_proof, proof) is False:
            proof += 1
        return proof

    @staticmethod
    def valid_proof(last_proof, proof):
        """
        Validates the Proof: Does hash(last_proof, proof) contain 4 leading zeros?
        """
        guess = f'{last_proof}{proof}'.encode()
        guess_hash = hashlib.sha256(guess).hexdigest()
        # You can change the difficulty by changing the number of leading zeros (e.g., '00000')
        return guess_hash[:4] == "0000"
    def is_chain_valid(self, chain):
        """
        Determine if a given blockchain is valid by verifying hashes.
        """
        last_block = chain[0]
        current_index = 1

        while current_index < len(chain):
            block = chain[current_index]
            
            # 1. Check that the previous_hash of the block is correct
            if block['previous_hash'] != self.hash(last_block):
                print(f"Invalid Chain: Block {current_index} hash mismatch.")
                return False

            # 2. Check that the Proof of Work is correct
            # Use the static method valid_proof already defined in your class
            if not self.valid_proof(last_block['proof'], block['proof']):
                print(f"Invalid Chain: Block {current_index} proof of work is invalid.")
                return False

            last_block = block
            current_index += 1

        return True

# Note: The global 'lms_blockchain' instance is correctly removed.