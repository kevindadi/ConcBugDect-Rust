# Explainer site

Static lesson for ConcBugDect-Rust. It shows one Petri net firing, then deadlock, data race, and atomicity violation on small nets, then the analysis pipeline and where translation, the `unipn` library, and the detectors sit.

No build step. From the repository root:

```bash
python3 -m http.server -d web 8080
```

Open `http://127.0.0.1:8080/`. Opening `web/index.html` in a browser also works.

## GitHub Pages

The site is served only after this folder is on the default branch and Pages is turned on. A pull request branch does not publish it.

In the repository on GitHub: **Settings → Pages → Build and deployment**

- Source: **Deploy from a branch**
- Branch: **`main`**
- Folder: **`/web`**

Save. The project URL is `https://kevindadi.github.io/ConcBugDect-Rust/`.

`web/.nojekyll` is present so Pages serves the files as written.

## License

MIT. Copyright (c) 2025 Kaiwen Zhang. See [LICENSE](LICENSE).
