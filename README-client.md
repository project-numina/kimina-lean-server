# Lean verification client

Client SDK to interact with the anonymized Lean verification server.

Example use:
```python
from lean_verification_client import LeanVerificationClient

# Specify LEAN_SERVER_API_KEY in your .env or pass `api_key`.
# Default `api_url` is https://example.com
client = LeanVerificationClient()

# If running locally use:
# client = LeanVerificationClient(api_url="http://localhost:80")

client.check("#check Nat")
```

## Backward client

```python
from lean_verification_client import Lean4Client

client = Lean4Client()

client.verify("#check Nat")
```