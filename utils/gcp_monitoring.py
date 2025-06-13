from google.cloud import monitoring_v3
from google.protobuf.timestamp_pb2 import Timestamp
import time
from collections import defaultdict
from threading import Lock

import requests

from server.config import settings

from loguru import logger


PROJECT_ID = settings.GCP_PROJECT_ID


monitoring_client = monitoring_v3.MetricServiceClient()
project_name = f"projects/{PROJECT_ID}"

RESOURCE_TYPE = "gce_instance"
RESOURCE_LABELS = {}

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
        f"[GCP Monitoring]Finally used resource type: {RESOURCE_TYPE}, label: {RESOURCE_LABELS}"
    )
else:
    logger.info("[GCP Monitoring]GCP project ID is not set, skipping GCP monitoring")

metric_cache = defaultdict(int)
cache_lock = Lock()
last_send_time = time.time()
SEND_INTERVAL = 60


def send_cached_metrics():
    global last_send_time
    current_time = time.time()

    if current_time - last_send_time >= SEND_INTERVAL:
        metrics_to_send = {}
        with cache_lock:
            if metric_cache:
                metrics_to_send = dict(metric_cache)
                metric_cache.clear()
                last_send_time = current_time
        
        for metric_name, metric_value in metrics_to_send.items():
            try:
                logger.debug(
                    f"[GCP Monitoring]Sending cached metric {metric_name}: {metric_value}"
                )
                send_event_metric(metric_name, metric_value)
            except Exception as e:
                logger.error(
                    f"[GCP Monitoring]Error sending cached metric {metric_name}: {e}"
                )


def send_event_metric(
    metric_name: str, metric_value: int, metric_labels: dict | None = None
):
    """
    Sends a metric data point to Cloud Monitoring indicating that an event occurred.

    Args:
    metric_name (str): The name of a custom metric, e.g. 'successful_requests_total'.
    metric_value (int): The value of the event, e.g. '1' for one occurrence.
    metric_labels (dict, optional): Additional metric labels, e.g. {'endpoint': '/data'}.
    """
    try:
        series = monitoring_v3.TimeSeries()
        series.metric.type = f"custom.googleapis.com/lean4_server/{metric_name}"

        if metric_labels:
            for key, value in metric_labels.items():
                series.metric.labels[key] = str(value)

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

        monitoring_client.create_time_series(name=project_name, time_series=[series])
    except Exception as e:
        logger.error(f"[GCP Monitoring]Error sending metric {metric_name}: {e}")


def record_metric(metric_name: str, metric_value: int = 1):
    with cache_lock:
        metric_cache[metric_name] += metric_value
