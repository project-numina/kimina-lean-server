import asyncio
import requests
from google.cloud import monitoring_v3
from google.protobuf.timestamp_pb2 import Timestamp
import time
from collections import defaultdict

from server.config import settings

from loguru import logger


PROJECT_ID = settings.GCP_PROJECT_ID


monitoring_client = monitoring_v3.MetricServiceClient()
project_name = f"projects/{PROJECT_ID}"

SEND_INTERVAL = settings.METRIC_UPDATE_INTERVAL

RESOURCE_TYPE = "gce_instance"
RESOURCE_LABELS = {}

# Initialize metadata on gcp VM instance
if PROJECT_ID:
    try:
        metadata_url = "http://metadata.google.internal/computeMetadata/v1/instance/"
        headers = {"Metadata-Flavor": "Google"}

        instance_id = requests.get(f"{metadata_url}id", headers=headers, timeout=2).text
        zone_full_path = requests.get(
            f"{metadata_url}zone", headers=headers, timeout=2
        ).text

        zone = zone_full_path.split("/")[-1]

        RESOURCE_LABELS = {
            "project_id": PROJECT_ID,
            "instance_id": instance_id,
            "zone": zone,
        }

        logger.info(
            f"[GCP Monitoring]GCP Compute Engine instance detected: {instance_id} in zone {zone}"
        )

    except requests.exceptions.RequestException as e:
        raise e

    logger.info(
        f"[GCP Monitoring]Finally used resource type: {RESOURCE_TYPE}, label: {RESOURCE_LABELS}, metric update interval: {SEND_INTERVAL}"
    )
else:
    logger.info("[GCP Monitoring]GCP project ID is not set, skipping GCP monitoring")

metric_cache = defaultdict(int)
cache_lock = asyncio.Lock()
last_send_time = time.time()


async def send_cached_metrics():
    """Send cached metrics asynchronously"""
    global last_send_time
    current_time = time.time()

    if current_time - last_send_time >= SEND_INTERVAL:
        metrics_to_send = {}
        async with cache_lock:
            if metric_cache:
                metrics_to_send = dict(metric_cache)
                metric_cache.clear()
                last_send_time = current_time
        
        # Send all metrics in a single batch to avoid GCP rate limiting
        if metrics_to_send:
            try:
                logger.debug(
                    f"[GCP Monitoring]Sending batch of {len(metrics_to_send)} metrics"
                )
                await send_batch_metrics(metrics_to_send)
            except Exception as e:
                logger.error(
                    f"[GCP Monitoring]Error sending batch metrics: {e}"
                )


async def send_batch_metrics(metrics_dict: dict):
    """Send multiple metrics in a single batch request"""
    try:
        time_series_list = []
        
        for metric_name, metric_value in metrics_dict.items():
            series = monitoring_v3.TimeSeries()
            series.metric.type = f"custom.googleapis.com/lean4_server/{metric_name}"

            series.resource.type = RESOURCE_TYPE
            for key, value in RESOURCE_LABELS.items():
                series.resource.labels[key] = str(value)

            now_timestamp = time.time()
            seconds = int(now_timestamp)
            nanos = int((now_timestamp - seconds) * 10**9)

            point = monitoring_v3.Point()

            end_time = Timestamp(seconds=seconds, nanos=nanos)
            start_time = Timestamp(seconds=seconds, nanos=nanos)

            point.interval = monitoring_v3.TimeInterval(
                end_time=end_time, start_time=start_time
            )

            point.value.int64_value = metric_value
            series.points.append(point)
            time_series_list.append(series)

        # Send all metrics in a single batch request
        if time_series_list:
            loop = asyncio.get_event_loop()
            request = monitoring_v3.CreateTimeSeriesRequest(
                name=project_name,
                time_series=time_series_list
            )
            await loop.run_in_executor(
                None, 
                monitoring_client.create_time_series,
                request
            )
            logger.debug(f"[GCP Monitoring]Successfully sent batch of {len(time_series_list)} metrics")
            
    except Exception as e:
        logger.error(f"[GCP Monitoring]Error sending batch metrics: {e}")


async def record_metric(metric_name: str, metric_value: int = 1):
    """Record a metric asynchronously"""
    async with cache_lock:
        metric_cache[metric_name] += metric_value
