import os
import json

def move_rulesets_out_of_completed_jobs(directory, w_directory):
    # Get list of directories in the specified directory
    directories = [d for d in os.listdir(directory) if os.path.isdir(os.path.join(directory, d))]
    
    for folder in directories:
        # Path to the ruleset.json file within each directory
        ruleset_path = os.path.join(directory, folder, 'rulesets', 'ruleset.json')
        
        # Check if the ruleset.json file exists
        if os.path.exists(ruleset_path):
            # Extract the integer n from the directory name
            n = folder.split('-')[-1]

            # Read ruleset.json
            with open(ruleset_path, 'r') as f:
                ruleset_data = json.load(f)

            # Write the combined JSON file
            output_filename = f"{n}.json"
            output_path = os.path.join(w_directory, output_filename)
            with open(output_path, 'w') as f:
                json.dump(ruleset_data, f, indent=4)

            print(f"Created {output_filename} from {ruleset_path}")

# Specify the directory path
directory_path = 'jobs'
write_directory_path = 'rulesets'

# Call the function
move_rulesets_out_of_completed_jobs(directory_path, write_directory_path)