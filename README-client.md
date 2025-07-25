# Kimina client

Client SDK to interact with Kimina Lean server. 

Example use:
```python
from kimina import Kimina

# Specify LEAN_SERVER_API_KEY in your .env or pass `api_key`.
# Default `api_url` is https://projectnumina.ai
client = Kimina()

# If running locally use:
# client = Kimina(api_url="http://localhost:80")

client.check("#check Nat")
```

## Backward client

```python
from kimina import Lean4Client

client = Lean4Client()

client.verify("#check Nat")
```