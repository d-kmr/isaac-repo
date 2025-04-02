from z3 import Solver, Bool, sat
import subprocess
import tempfile
import itertools

def extract_implicants_z3(formula):
    solver = Solver()
    solver.add(formula)

    variables = list(set(str(v) for v in formula.children()))
    num_vars = len(variables)

    implicants = []
    while solver.check() == sat:
        model = solver.model()
        assignment = "".join('1' if model[Bool(v)] else '0' for v in variables)
        implicants.append((assignment, '1')) 

       
        blocking_clause = [Bool(v) if model[Bool(v)] else ~Bool(v) for v in variables]
        solver.add(~formula | ~blocking_clause[0])  

    print("Extracted Implicants:", implicants)
    return variables, implicants


def boolean_to_pla(variables, implicants):
    num_inputs = len(variables)
    pla_content = f".i {num_inputs}\n.o 1\n"

    for input_bits, output_bit in implicants:
        pla_content += f"{input_bits} {output_bit}\n"

    pla_content += ".e\n"
    
    print("Generated PLA File:\n", pla_content) 
    return pla_content


def run_espresso(pla_input):
    with tempfile.NamedTemporaryFile(delete=False) as temp_file:
        temp_file.write(pla_input.encode())
        temp_file.flush()

        result = subprocess.run(["espresso", temp_file.name], capture_output=True, text=True)

        print("Espresso Output:\n", result.stdout) 
        print("Espresso Errors:\n", result.stderr) 

        return result.stdout



a, b, c = Bool("a"), Bool("b"), Bool("c")
formula = (a | b) & (a | c)


variables, implicants = extract_implicants_z3(formula)


pla_data = boolean_to_pla(variables, implicants)


minimized_result = run_espresso(pla_data)

print("Minimized Boolean Function:\n", minimized_result)
