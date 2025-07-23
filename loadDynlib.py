import stat
import os

base = os.path.dirname(os.path.abspath(__file__))
path = f"{base}/repl/REPL/Main.lean"
path_to_leangeo = f"{base}/LeanGeo"
text = f"  Lean.loadDynlib \"{path_to_leangeo}/.lake/packages/cvc5/.lake/build/lib/libcvc5-1.so\""

print(f"Switch to r&w privilege for {path}.")
os.chmod(path, stat.S_IRWXU)

print(f"Modifying REPL, fixing shared library bug.")
fp = open(path, 'r')           
s = fp.read()                   
fp.close()                      
a = s.split('\n')
a.insert(292, text)    
s = '\n'.join(a)             
fp = open(path, 'w')
fp.write(s)
fp.close()