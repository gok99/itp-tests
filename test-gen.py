#!/usr/bin/env python3

import os

# Directory containing the test case files
test_case_dir = 'programs'

# Template file to fill in
template_file = 'hoare_template.py'

# Output file name pattern
output_file_pattern = 'hoare_templates_{}.py'

def read_test_case(file_path):
    with open(file_path, 'r') as f:
        sections = f.read().split('\n\n')
        
        program = sections[0].strip()
        triple = sections[1].strip()
        input_data = sections[2].strip()
        prepost = sections[3].strip()
        
        # Split the prepost section into pre and post
        # Find the lines starting with P and Q
        lines = prepost.split('\n')
        pre = next(line for line in lines if line.startswith('P = '))
        post = next(line for line in lines if line.startswith('Q = '))
        
        return program, triple, input_data, pre, post

def fill_template(template, program, triple, input_data, pre, post):
    template = template.replace('<PROGRAM>', program)
    template = template.replace('<TRIPLE>', triple)
    template = template.replace('<INPUT>', input_data)
    template = template.replace('<PRE>', pre)
    template = template.replace('<POST>', post)
    return template

# Read the template file
with open(template_file, 'r') as f:
    template = f.read()

# Process each test case file
for filename in os.listdir(test_case_dir):
    if filename.endswith('.test'):
        test_case_path = os.path.join(test_case_dir, filename)
        program, triple, input_data, pre, post = read_test_case(test_case_path)
        
        output_filename = output_file_pattern.format(filename.split('.')[0])
        output_path = os.path.join(os.path.dirname(__file__), output_filename)
        
        filled_template = fill_template(template, program, triple, input_data, pre, post)
        
        with open(output_path, 'w') as f:
            f.write(filled_template)
        
        print(f"Generated {output_filename} from {filename}")
