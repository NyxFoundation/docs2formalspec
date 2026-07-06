"""CLI: d2fs run --name apyx URL [URL ...]"""

from __future__ import annotations

import typer

from .config import Config
from .pipeline import relean as relean_pipeline
from .pipeline import run as run_pipeline

app = typer.Typer(add_completion=False)


@app.command()
def version():
    """Print version."""
    from . import __version__

    typer.echo(__version__)


@app.command()
def run(
    sources: list[str] = typer.Argument(..., help="Doc URLs or file paths"),
    name: str = typer.Option(..., "--name", "-n", help="System/protocol name"),
):
    """Generate RFC2119 spec + Lean4 formalization from documentation sources."""
    result = run_pipeline(name, sources, Config())
    typer.echo(result)


@app.command()
def relean(name: str = typer.Option(..., "--name", "-n", help="System/protocol name")):
    """Re-run only the Lean generation stage from saved requirements/model."""
    result = relean_pipeline(name, Config())
    typer.echo(result)


if __name__ == "__main__":
    app()
