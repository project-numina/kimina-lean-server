from fastapi import HTTPException, Security
from fastapi.security.api_key import APIKeyHeader

from .settings import settings

api_key_header = APIKeyHeader(name="X-Auth-Token", auto_error=False)

# TODO: Implement key in db once ready
# async def seed_key():
#     if db.connected:
#     existing = await db.client.api_key.find_first()
#     if not existing:
#         await db.client.api_key.create(data={"key": API_KEY})


async def require_key(auth: str = Security(api_key_header)) -> str | None:
    if settings.api_key is None:
        return None

    if not auth:
        raise HTTPException(401, "Missing API key")

    token = auth.removeprefix("Bearer ").strip()
    # found = await db.client.api_key.find_unique(where={"key": token})
    if not token == settings.api_key:
        raise HTTPException(status_code=401, detail="Invalid API key")
    return token
