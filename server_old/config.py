import os

from pydantic import Field, ValidationError, field_validator
from pydantic_settings import BaseSettings, SettingsConfigDict


class Settings(BaseSettings):
    HOST: str = Field("0.0.0.0")
    PORT: int = Field(12332)
    API_KEY: str | None = Field(None)
    LOG_DIR: str = Field("./logs")
    LOG_LEVEL: str = Field("INFO")
    WORKSPACE: str = Field(default_factory=os.getcwd)
    MAX_REPLS: int = Field(os.cpu_count() or 1)
    MAX_CONCURRENT_REQUESTS: int = Field(os.cpu_count() or 1)
    REPL_MEMORY_LIMIT_GB: int | None = Field(None)
    HARD_ENFORCE_MEMORY_LIMIT: bool = Field(False)
    REPL_MEMORY_CHECK_INTERVAL: int | None = Field(None)
    HEALTHCHECK_CPU_USAGE_THRESHOLD: int | None = Field(None)
    HEALTHCHECK_MEMORY_USAGE_THRESHOLD: int | None = Field(None)

    model_config = SettingsConfigDict(
        env_file=".env", env_file_encoding="utf-8", env_prefix="LEANSERVER_"
    )

    @field_validator("WORKSPACE", mode="before")
    @classmethod
    def validate_workspace(cls, v):
        if v == "":
            return os.getcwd()
        return v

    @field_validator("API_KEY", mode="before")
    @classmethod
    def validate_api_key(cls, v):
        if v == "":
            return None
        return v

    @field_validator("MAX_REPLS", mode="before")
    @classmethod
    def validate_max_repls(cls, v):
        if v == "":
            return os.cpu_count() or 1
        return v

    @field_validator("MAX_CONCURRENT_REQUESTS", mode="before")
    @classmethod
    def validate_max_concurrent_requests(cls, v):
        if v == "":
            return os.cpu_count() or 1
        return v

    @field_validator("HEALTHCHECK_CPU_USAGE_THRESHOLD", mode="before")
    @classmethod
    def validate_healthcheck_cpu_usage_threshold(cls, v):
        if v == "":
            return None
        return v

    @field_validator("HEALTHCHECK_MEMORY_USAGE_THRESHOLD", mode="before")
    @classmethod
    def validate_healthcheck_memory_usage_threshold(cls, v):
        if v == "":
            return None
        return v

    @field_validator("REPL_MEMORY_LIMIT_GB", mode="before")
    @classmethod
    def validate_repl_memory_limit_gb(cls, v):
        if v == "":
            return None
        return v

    @field_validator("REPL_MEMORY_CHECK_INTERVAL", mode="before")
    @classmethod
    def validate_repl_memory_check_interval(cls, v):
        if v == "":
            return None
        return v

    @field_validator("HARD_ENFORCE_MEMORY_LIMIT", mode="before")
    @classmethod
    def validate_hard_enforce_memory_limit(cls, v):
        if v == "":
            return False
        return v

try:
    settings = Settings()
except ValidationError as e:
    missing_vars = [
        f"LEANSERVER_{str(err['loc'][0]).upper()}"
        for err in e.errors()
        if err["type"] == "missing"
    ]
    raise ValueError(f"Missing environment variables: {', '.join(missing_vars)}")
