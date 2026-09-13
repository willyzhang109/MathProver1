"""Request and response schemas."""

from typing import List, Optional

from pydantic import BaseModel, Field

from .config import settings


class FormalizeRequest(BaseModel):
    nl: str = Field(min_length=1, max_length=settings.max_nl_chars)


class CheckRequest(BaseModel):
    lean: str = Field(min_length=1, max_length=settings.max_lean_chars)


class JobRequest(BaseModel):
    mode: str = Field(pattern="^(lean|nl)$")
    lean: str = Field(min_length=1, max_length=settings.max_lean_chars)
    nl: Optional[str] = Field(default=None, max_length=settings.max_nl_chars)


class CancelResponse(BaseModel):
    id: str
    phase: str
