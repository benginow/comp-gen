import json
from enum import Enum
from itertools import product

class Operations(Enum):
    # Won't run algorithm until later
    # Algorithm = "Algorithm"
    HandPicked = "HandPicked"
    HandPickedThinner = "HandPickedThinner"
    AllAtOnce = "AllAtOnce"


class SynthesisConfig:
    def __init__(self, operation_matching, canon_force, arity_shorting):
        self.operation_matching = operation_matching
        self.canon_force = canon_force
        self.arity_shorting = arity_shorting

def generate_json_file(config, filename):
    data = {
        "name": filename,
        "operation_matching": config.operation_matching.value,
        "canon_force": config.canon_force,
        "arity_shorting": config.arity_shorting
    }
    with open(filename, 'w') as f:
        json.dump(data, f, indent=4)

i=0
# Generate all possible configurations
for operation_matching, canon_force, arity_shorting in product(Operations, [True, False], [True, False]):
    config = SynthesisConfig(operation_matching, canon_force, arity_shorting)
    filename = f"{i+1}.json"
    i=i+1
    generate_json_file(config, filename)