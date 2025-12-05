# Contributing

## Workflow

**Work items** → GitHub Issues  
**Chat** → [Discord](https://discord.gg/Msh3XHs3WR)

## Getting started

1. Fork the repository
2. Clone your fork locally
3. Add upstream remote: `git remote add upstream https://github.com/DanielBrockhaus/astonia_community_client.git`

## Picking up work

1. Check [Issues](../../issues) for something to work on
2. Comment on the issue to claim it (or assign yourself if you have access)
3. Sync your fork: `git fetch upstream && git rebase upstream/main`
4. Create a branch, prefix with issue number: `42-fix-inventory-crash`

## Pull requests

1. Push your branch to your fork
2. Open a PR against `main`
3. Reference the issue: `Fixes #42`
4. **Wait for all CI checks to pass before requesting review**
5. If checks fail, fix them first - don't ask others to review broken code

## Issues

- **Dependencies:** List them as task checkboxes linking to other issues
- **Blocked?** Note what you're waiting on in a comment
- **Stuck?** Ping in Discord or comment on the issue

## Code

- Keep commits atomic
- Test your changes locally before PR
- If it touches gameplay, note how to test it in the PR description

## Labels

| Label | Meaning |
|-------|---------|
| `bug` | Broken behavior |
| `enhancement` | New feature |
| `blocked` | Waiting on something |
| `good first issue` | Smaller, self-contained |

## Questions?

Jump into [Discord](https://discord.gg/Msh3XHs3WR) or open an Issue.
