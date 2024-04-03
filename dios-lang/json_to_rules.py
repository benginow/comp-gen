import json

def json_to_formula(json_data):
    lhs = json_data["lhs"]
    rhs = json_data["rhs"]
    bidirectional = json_data["bidirectional"]

    if bidirectional:
        return f"{lhs} <==> {rhs}\n"
    else:
        return f"{lhs} ==> {rhs}\n"
    
def main():
    with open("rational_rules.json", "r") as file:
        json_data = json.load(file)
        json_rules = json_data.get("eqs", [])


    with open("rational_rules.txt", "w") as write_file:
        for rule in json_rules:
            formula = json_to_formula(rule)
            write_file.write(formula)

if __name__ == "__main__":
    main()