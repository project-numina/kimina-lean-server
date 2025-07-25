from fastapi import HTTPException, Security
from fastapi.security.api_key import APIKeyHeader

from .settings import settings
from .db import db

api_key_header = APIKeyHeader(name="Authorization", auto_error=False)

# TODO: Implement key in db once ready
# async def seed_key():
#     if db.connected:
#     existing = await db.client.api_key.find_first()
#     if not existing:
#         await db.client.api_key.create(data={"key": API_KEY})


async def require_key(auth: str = Security(api_key_header)) -> str | None:
    if settings.api_key is None and not db.connected:
        return None

    if not auth:
        raise HTTPException(401, "Missing API key")

    token = auth.removeprefix("Bearer ").strip()

    if settings.api_key and token == settings.api_key:
        return token

    if db.connected:
        found = await db.client.api_key.find_first(where={"key": token})
        if found:
            return token

    raise HTTPException(status_code=401, detail="Invalid API key")
