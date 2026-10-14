"""Installed profitability policy; never an applicability or correctness premise."""
import json
from importlib.resources import files

def policy():
    value=json.loads(files('ink_knowledge').joinpath('state-selection.json').read_text())
    if set(value)!={'schema','minimum_processes','minimum_rounds','scope'} or value['schema']!=1 or not isinstance(value['scope'],str):raise ValueError('state selection policy schema')
    for name,lo,hi in [('minimum_processes',3,8),('minimum_rounds',9,64)]:
        if type(value[name])is not int or not lo<=value[name]<=hi:raise ValueError('state selection '+name)
    return value
