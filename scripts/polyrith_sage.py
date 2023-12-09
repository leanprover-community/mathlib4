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
    var_list = ", ".join([f"var{i}" for i in range(n_vars)])
    query = f'''
if {n_vars!r} != 0:
    P = PolynomialRing({type_str(type)}, 'var', {n_vars!r})
    [{var_list}] = P.gens()
else:
    # workaround for a Sage shortcoming with `n_vars = 0`,
    # `TypeError: no conversion of this ring to a Singular ring defined`
    P = PolynomialRing({type_str(type)}, 'var', 1)
p = P({goal_type})
I = P.ideal({eq_list})
coeffs = p.lift(I)
print(serialize_polynomials(coeffs))
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
    1 - a string containing "true" or "false" depending on whether polyrith was called with trace enabled
    2 - a string representing the base type of the target
    3 - the number of variables used
    4 - a list of the polynomial hypotheses/proof terms in terms of the variables
    5 - a single polynomial representing the target

    This returns a json object with format:
    ```
    { success: bool,
      data: Optional[list[str]],
      trace: Optional[str],
      name: Optional[str],
      value: Optional[str] }
    ```
    '''
    command = create_query(sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5])
    final_query = polynomial_formatting_functions + "\n" + command
    if sys.argv[1] == 'true': # trace dry run enabled
        output = dict(success=True, trace=command)
    else:
        try:
            output = dict(success=True, data=evaluate_in_sage(final_query))
        except EvaluationError as e:
            output = dict(success=False, name=e.ename, value=e.evalue)
    print(json.dumps(output))

if __name__ == "__main__":
    main()
