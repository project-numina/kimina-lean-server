import asyncio
from google.cloud import logging as gcp_logging
from loguru import logger
from server.config import settings

PROJECT_ID = settings.GCP_PROJECT_ID
LOG_NAME = "lean_server"

if PROJECT_ID:
    try:
        logging_client = gcp_logging.Client(project=PROJECT_ID)
        cloud_logger = logging_client.logger(LOG_NAME)
        logger.info(f"[GCP Logging] Initialized cloud logger '{LOG_NAME}' for project {PROJECT_ID}")
    except Exception as e:
        cloud_logger = None
        logger.error(f"[GCP Logging] Failed to initialize client: {e}")
else:
    cloud_logger = None
    logger.info("[GCP Logging] GCP project ID is not set, skipping cloud logging")

async def log_struct(data: dict, severity: str = "INFO") -> None:
    if cloud_logger is None:
        return
    loop = asyncio.get_event_loop()
    try:
        await loop.run_in_executor(None, cloud_logger.log_struct, data, severity)
    except Exception as e:
        logger.error(f"[GCP Logging] Failed to send log: {e}")


async def log_verify_event(request_body: dict, response_body: dict | None = None) -> None:
    data = {"request": request_body}
    if response_body is not None:
        data["response"] = response_body
    await log_struct(data)

