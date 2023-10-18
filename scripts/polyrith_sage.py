# This file is part of the `polyrith` tactic in `src/tactic/polyrith.lean`.
# It interfaces between Lean and the Sage web interface.

import requests
import json
import sys
from os.path import join, dirname

# These functions are used to format the output of Sage for parsing in Lean.
# They are stored here as a string since they are passed to Sage via the web API.
with open(join(dirname(__file__), "polyrith_sage_helper.py"), encoding='utf8') as f:
    polynomial_formatting_functions = f.read()

# future extensions may change behavior depending on the base type
def type_str(type):
    return "QQ"

def create_query(type: str, n_vars: int, eq_list, goal_type):
    """ Create a query to invoke Sage's `MPolynomial_libsingular.lift`. See
    https://github.com/sagemath/sage/blob/f8df80820dc7321dc9b18c9644c3b8315999670b/src/sage/rings/polynomial/multi_polynomial_libsingular.pyx#L4472-L4518
    for a description of this method. """
    var_list = [f"var{i}" for i in range(n_vars)] + ['aux']
    query = f'''
import json
P = {type_str(type)}{var_list}
[{", ".join(var_list)}] = P.gens()
p = P({goal_type})
gens = {eq_list} + [1 - p*aux]
I = ideal(gens)
coeffs = P(1).lift(I)
power = max(cf.degree(aux) for cf in coeffs)
coeffs = [P(cf.subs(aux = 1/p)*p^power) for cf in coeffs[:int(-1)]]
js = {{'power': power, 'coeffs': [polynomial_to_string(c) for c in coeffs]}}
print(json.dumps(js))
'''
    return query

class EvaluationError(Exception):
    def __init__(self, ename, evalue, message='Error in Sage communication'):
        self.ename = ename
        self.evalue = evalue
        self.message = message
        super().__init__(self.message)

def evaluate_in_sage(query: str) -> str:
    data = {'code': query}
    headers = {'content-type': 'application/x-www-form-urlencoded'}
    response = requests.post('https://sagecell.sagemath.org/service', data, headers=headers).json()
    if response['success']:
        return json.loads(response.get('stdout'))
    elif 'execute_reply' in response and 'ename' in response['execute_reply'] and 'evalue' in response['execute_reply']:
        raise EvaluationError(response['execute_reply']['ename'], response['execute_reply']['evalue'])
    else:
        raise Exception(response)

def main():
    '''The system args contain the following:
    0 - the path to this python file
    1 - a string containing "tt" or "ff" depending on whether polyrith was called with trace enabled
    2 - a string representing the base type of the target
    3 - the number of variables used
    4 - a list of the polynomial hypotheses/proof terms in terms of the variables
    5 - a single polynomial representing the target

    This returns a json object with format:
    ```
    { success: bool,
      data: Optional[list[str]],
      trace: Optional[str],
      error_name: Optional[str],
      error_value: Optional[str] }
    ```
    '''
    command = create_query(sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5])
    final_query = polynomial_formatting_functions + "\n" + command
    if sys.argv[1] == 'tt': # trace dry run enabled
        output = dict(success=True, trace=command)
    else:
        try:
            output = dict(success=True, data=evaluate_in_sage(final_query))
        except EvaluationError as e:
            output = dict(success=False, error_name=e.ename, error_value=e.evalue)
    print(json.dumps(output))


if __name__ == "__main__":
    main()
