import os
import re
from typing import cast

from pydantic import Field, field_validator, model_validator
from pydantic_settings import BaseSettings, SettingsConfigDict


class Settings(BaseSettings):
    BASE: str = Field(default_factory=os.getcwd)
    repl_bin_path: str = ""
    path_to_mathlib: str | None = None
    LOG_LEVEL: str = "INFO"
    MAX_REPLS: int = 2
    MAX_USES: int = 1
    MAX_MEM: int = 8
    INIT_REPLS: dict[str, int] = Field(
        default_factory=lambda: {"import Mathlib\nimport Aesop": 1}
    )
    MAX_WAIT: int = 60

    DATABASE_USER: str = "root"
    DATABASE_PASSWORD: str = "root"
    DATABASE_NAME: str = "fastrepl"
    DATABASE_HOST: str = "localhost"
    DATABASE_PORT: int = 5432
    DATABASE_URL: str = "postgresql://root:root@localhost:5432/fastrepl"

    LEAN_VERSION: str = "v4.15.0"
    API_KEY: str | None = None

    model_config = SettingsConfigDict(
        env_file=".env", env_file_encoding="utf-8", env_prefix="LEANSERVER_"
    )

    @field_validator("MAX_MEM", mode="before")
    def _parse_max_mem(cls, v: str) -> int:
        if isinstance(v, int):
            return cast(int, v * 1024)
        m = re.fullmatch(r"(\d+)([MmGg])", v)
        if m:
            n, unit = m.groups()
            n = int(n)
            return n if unit.lower() == "m" else n * 1024
        raise ValueError("MAX_MEM must be an int or '<number>[M|G]'")

    @model_validator(mode="after")
    def set_defaults(self) -> "Settings":
        if self.repl_bin_path == "":
            self.repl_bin_path = self.BASE + "/repl/.lake/build/bin/repl"
        if self.path_to_mathlib is None:
            self.path_to_mathlib = self.BASE + "/mathlib4"
        return self


settings = Settings()
