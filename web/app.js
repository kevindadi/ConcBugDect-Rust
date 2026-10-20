"use strict";

(function () {
    function canFire(marking, transition) {
        return Object.entries(transition.inputs).every(function (entry) {
            return (marking[entry[0]] || 0) >= entry[1];
        });
    }

    function applyFire(marking, transition) {
        const next = Object.assign({}, marking);
        Object.entries(transition.inputs).forEach(function (entry) {
            next[entry[0]] -= entry[1];
        });
        Object.entries(transition.outputs).forEach(function (entry) {
            next[entry[0]] = (next[entry[0]] || 0) + entry[1];
        });
        return next;
    }

    function enabledIds(marking, transitions) {
        return Object.keys(transitions).filter(function (id) {
            return canFire(marking, transitions[id]);
        });
    }

    function compile(model) {
        let marking = Object.assign({}, model.initial);
        const trace = [];
        return model.script.map(function (step, index) {
            const enabledBefore = enabledIds(marking, model.transitions);
            if (step.fire && enabledBefore.indexOf(step.fire) === -1) {
                throw new Error(
                    model.id + " step " + index + " fires disabled " + step.fire +
                    " (enabled: " + enabledBefore.join(", ") + ")"
                );
            }
            const before = Object.assign({}, marking);
            if (step.fire) {
                const transition = model.transitions[step.fire];
                marking = applyFire(marking, transition);
                trace.push({
                    kind: transition.event.kind,
                    tid: transition.event.tid,
                    alias: transition.event.alias,
                    role: step.role || "",
                    label: transition.label
                });
            }
            const enabledAfter = enabledIds(marking, model.transitions);
            if (step.stuck && enabledAfter.length !== 0) {
                throw new Error(
                    model.id + " step " + index + " expected a stuck marking, enabled: " +
                    enabledAfter.join(", ")
                );
            }
            (step.expectEnabled || []).forEach(function (id) {
                if (enabledBefore.indexOf(id) === -1) {
                    throw new Error(model.id + " step " + index + " expected " + id + " enabled");
                }
            });
            return {
                title: step.title,
                body: step.body,
                inset: step.inset,
                fire: step.fire || null,
                stuck: Boolean(step.stuck),
                race: Boolean(step.race),
                witness: Boolean(step.witness),
                showEnabled: step.showEnabled !== false,
                waiting: step.waiting || [],
                notePlaces: step.notePlaces || [],
                before: before,
                after: Object.assign({}, marking),
                enabledBefore: enabledBefore,
                enabledAfter: enabledAfter,
                trace: trace.slice()
            };
        });
    }

    function firingModel() {
        return {
            id: "firing",
            label: "One Petri net firing: ready and mutex into held",
            viewBox: "0 0 720 300",
            tone: "place",
            places: {
                ready: { x: 140, y: 88, label: "ready" },
                mutex: { x: 140, y: 210, label: "mutex", resource: true },
                held: { x: 580, y: 150, label: "held" }
            },
            transitions: {
                lock: {
                    x: 360, y: 150, label: "lock", inputs: { ready: 1, mutex: 1 },
                    outputs: { held: 1 },
                    event: { kind: "Lock", tid: "T", alias: "M" }
                }
            },
            bends: {},
            initial: { ready: 1, mutex: 1, held: 0 },
            script: [
                {
                    title: "Places, a transition, tokens",
                    body: "Circles are places. The bar is a transition. A token means that place currently holds. ready and mutex each have one token. held is empty. The bar does not store tokens.",
                    inset: "marking\n  ready  •\n  mutex  •\n  held   ○",
                    showEnabled: false
                },
                {
                    title: "lock is enabled",
                    body: "A transition may fire only when every input place has the tokens its arc needs. Both inputs have a token, so lock is enabled. One token is the weight used for a mutex Lock in this analyzer.",
                    inset: "enabled\n  lock  ← ready, mutex",
                    expectEnabled: ["lock"]
                },
                {
                    title: "One firing",
                    body: "Firing takes one token from each input place and puts one token in held. The transition does not keep them. After this step lock is no longer enabled.",
                    inset: "after firing\n  ready  ○\n  mutex  ○\n  held   •",
                    fire: "lock"
                }
            ]
        };
    }

    function deadlockModel() {
        return {
            id: "deadlock",
            label: "AB-BA deadlock on two mutex places",
            viewBox: "0 0 900 520",
            tone: "stuck",
            bands: [
                { x: 28, y: 78, w: 700, h: 112, cls: "band" },
                { x: 28, y: 318, w: 700, h: 112, cls: "band-b" }
            ],
            places: {
                A: { x: 250, y: 252, label: "Mutex A", resource: true },
                B: { x: 470, y: 252, label: "Mutex B", resource: true },
                t1: { x: 90, y: 134, label: "T1 start" },
                holdsA: { x: 330, y: 134, label: "holds A" },
                done1: { x: 660, y: 134, label: "T1 done" },
                t2: { x: 90, y: 374, label: "T2 start" },
                holdsB: { x: 330, y: 374, label: "holds B" },
                done2: { x: 660, y: 374, label: "T2 done" },
                main_end: { x: 810, y: 252, label: "main_end", ghost: true, r: 20 }
            },
            transitions: {
                lockA1: {
                    x: 200, y: 134, label: "Lock A", sub: "T1",
                    inputs: { t1: 1, A: 1 }, outputs: { holdsA: 1 },
                    event: { kind: "Lock", tid: "T1", alias: "A" }
                },
                lockB1: {
                    x: 500, y: 134, label: "Lock B", sub: "T1",
                    inputs: { holdsA: 1, B: 1 }, outputs: { done1: 1 },
                    event: { kind: "Lock", tid: "T1", alias: "B" }
                },
                lockB2: {
                    x: 200, y: 374, label: "Lock B", sub: "T2",
                    inputs: { t2: 1, B: 1 }, outputs: { holdsB: 1 },
                    event: { kind: "Lock", tid: "T2", alias: "B" }
                },
                lockA2: {
                    x: 500, y: 374, label: "Lock A", sub: "T2",
                    inputs: { holdsB: 1, A: 1 }, outputs: { done2: 1 },
                    event: { kind: "Lock", tid: "T2", alias: "A" }
                }
            },
            bends: {
                "A->lockA2": 36,
                "B->lockB1": -36
            },
            initial: {
                A: 1, B: 1, t1: 1, t2: 1,
                holdsA: 0, holdsB: 0, done1: 0, done2: 0, main_end: 0
            },
            script: [
                {
                    title: "Two threads, two mutexes",
                    body: "Thread 1 will lock A, then B. Thread 2 will lock B, then A. Each Lock needs the thread's token and one token from that mutex place. main_end is empty: the entry function has not finished.",
                    inset: "T1: start → Lock A → holds A → Lock B → done\nT2: start → Lock B → holds B → Lock A → done\nmain_end ○",
                    showEnabled: false
                },
                {
                    title: "The first locks are enabled",
                    body: "Lock A on thread 1 and Lock B on thread 2 can both fire. The opposite order is also enabled. The schedule that follows is the one that gets stuck.",
                    inset: "enabled now\n  T1 Lock A\n  T2 Lock B",
                    expectEnabled: ["lockA1", "lockB2"]
                },
                {
                    title: "Thread 1 takes Mutex A",
                    body: "Lock A fires. Thread 1 holds A, and Mutex A is empty. Thread 1 can still lock B, and thread 2 can still lock B. Both of those bars are enabled.",
                    inset: "s0 --Lock A--> s1\nenabled from s1\n  T1 Lock B\n  T2 Lock B",
                    fire: "lockA1",
                    expectEnabled: ["lockA1"]
                },
                {
                    title: "Thread 2 takes Mutex B",
                    body: "Lock B on thread 2 fires. Both mutex places are now empty. The dashed bars are the locks that still need a token and cannot fire. No transition is enabled, and main_end still has no token.",
                    inset: "s1 --Lock B--> s2\ns2 has no outgoing edge\nmain_end has no token",
                    fire: "lockB2",
                    expectEnabled: ["lockB1", "lockB2"],
                    stuck: true,
                    waiting: ["lockB1", "lockA2"],
                    notePlaces: ["main_end"]
                }
            ]
        };
    }

    function raceModel() {
        return {
            id: "race",
            label: "Data race: UnsafeWrite and UnsafeRead enabled together on L",
            viewBox: "0 0 720 380",
            tone: "race",
            bands: [
                { x: 36, y: 64, w: 650, h: 92, cls: "band" },
                { x: 36, y: 250, w: 650, h: 92, cls: "band-b" }
            ],
            places: {
                i0: { x: 110, y: 110, label: "thread i" },
                i1: { x: 590, y: 110, label: "after i" },
                j0: { x: 110, y: 296, label: "thread j" },
                j1: { x: 590, y: 296, label: "after j" }
            },
            transitions: {
                write: {
                    x: 350, y: 110, label: "UnsafeWrite",
                    inputs: { i0: 1 }, outputs: { i1: 1 },
                    event: { kind: "UnsafeWrite", tid: "i", alias: "L" }
                },
                read: {
                    x: 350, y: 296, label: "UnsafeRead",
                    inputs: { j0: 1 }, outputs: { j1: 1 },
                    event: { kind: "UnsafeRead", tid: "j", alias: "L" }
                }
            },
            bends: {},
            chip: { x: 350, y: 196, w: 168, h: 34, text: "location L" },
            initial: { i0: 1, i1: 0, j0: 1, j1: 0 },
            script: [
                {
                    title: "Two accesses, one location",
                    body: "Each unsafe access is a transition. It needs only its own thread token. Location L is the alias stored on the transition. L is not a place, and neither bar consumes a token from it.",
                    inset: "thread i → UnsafeWrite(L)\nthread j → UnsafeRead(L)\nlocation_id = L",
                    showEnabled: false
                },
                {
                    title: "Both are enabled in one marking",
                    body: "From this marking both bars are outgoing edges. DataRaceDetector groups those enabled accesses by location_id. A write paired with a read on L is a data race. A second UnsafeWrite on L would count too. Read paired only with read does not.",
                    inset: "marking s\n  |-- UnsafeWrite(L)\n  |-- UnsafeRead(L)\nsame location, one write",
                    expectEnabled: ["write", "read"],
                    race: true
                }
            ]
        };
    }

    function atomicityModel(kind) {
        const patterns = {
            AV1: { first: "AtomicLoad", firstKind: "Load", second: "AtomicStore", secondKind: "Store", midLabel: "after load" },
            AV2: { first: "AtomicStore", firstKind: "Store", second: "AtomicLoad", secondKind: "Load", midLabel: "after store" },
            AV3: { first: "AtomicLoad", firstKind: "Load", second: "AtomicLoad", secondKind: "Load", midLabel: "after load" }
        };
        const pattern = patterns[kind];
        return {
            id: "atom-" + kind,
            kind: kind,
            label: kind + " witness on one atomic alias",
            viewBox: "0 0 860 360",
            tone: "atom",
            bands: [
                { x: 28, y: 58, w: 800, h: 88, cls: "band" },
                { x: 28, y: 210, w: 800, h: 88, cls: "band-b" }
            ],
            places: {
                i0: { x: 70, y: 102, label: "thread i" },
                iMid: { x: 400, y: 102, label: pattern.midLabel },
                i1: { x: 760, y: 102, label: "thread i done" },
                j0: { x: 70, y: 254, label: "thread j" },
                j1: { x: 620, y: 254, label: "thread j done" }
            },
            transitions: {
                iFirst: {
                    x: 230, y: 102, label: pattern.first, sub: "i",
                    inputs: { i0: 1 }, outputs: { iMid: 1 },
                    event: { kind: pattern.firstKind, tid: "i", alias: "L" }
                },
                iSecond: {
                    x: 580, y: 102, label: pattern.second, sub: "i",
                    inputs: { iMid: 1 }, outputs: { i1: 1 },
                    event: { kind: pattern.secondKind, tid: "i", alias: "L" }
                },
                jStore: {
                    x: 340, y: 254, label: "AtomicStore", sub: "j",
                    inputs: { j0: 1 }, outputs: { j1: 1 },
                    event: { kind: "Store", tid: "j", alias: "L" }
                }
            },
            bends: {},
            chip: { x: 430, y: 178, w: 150, h: 34, text: "atomic L" },
            initial: { i0: 1, iMid: 0, i1: 0, j0: 1, j1: 0 },
            script: [
                {
                    title: kind + " starts at the initial marking",
                    body: "Thread i has two atomic events. Thread j has a store on the same alias L. No mutex sits between them, so the store can fire in the middle of i's interval. The detector walks a path of the state graph; this step has not moved yet.",
                    inset: kind + " shape\n  start on i, store on j, end on i\n  same alias, j ≠ i",
                    showEnabled: false
                },
                {
                    title: "Start on thread i",
                    body: "The first event on thread i fires. That is the start of the interval. Thread j's store is still enabled.",
                    inset: "start  " + pattern.first + "  thread i",
                    fire: "iFirst",
                    role: "start"
                },
                {
                    title: "A remote store",
                    body: "Thread j's AtomicStore fires before thread i finishes the interval. The witness rule requires this middle event to be a store, on the same alias, from a different thread.",
                    inset: "start on i\nmid    AtomicStore  thread j",
                    fire: "jStore",
                    role: "mid"
                },
                {
                    title: kind + " witness",
                    body: "Thread i's second event fires. Start, then the remote store, then the end: that order, on one alias, is an " + kind + " witness. AtomicCmpXchg would count as a store the same way AtomicStore does.",
                    inset: "",
                    fire: "iSecond",
                    role: "end",
                    witness: true
                }
            ]
        };
    }

    function selfCheck() {
        const firing = compile(firingModel());
        const fired = firing[2];
        if (fired.after.held !== 1 || fired.after.ready !== 0 || fired.after.mutex !== 0) {
            throw new Error("firing marking");
        }
        if (fired.enabledAfter.length !== 0) throw new Error("lock still enabled");

        const dead = compile(deadlockModel());
        if (dead[1].enabledBefore.slice().sort().join() !== "lockA1,lockB2") {
            throw new Error("initial AB-BA enabling");
        }
        if (dead[3].enabledBefore.slice().sort().join() !== "lockB1,lockB2") {
            throw new Error("choice before the stuck lock");
        }
        const stuck = dead[3];
        if (stuck.after.A !== 0 || stuck.after.B !== 0 || stuck.after.holdsA !== 1 || stuck.after.holdsB !== 1) {
            throw new Error("stuck token placement");
        }
        if (stuck.after.main_end !== 0 || stuck.after.done1 !== 0 || stuck.after.done2 !== 0) {
            throw new Error("stuck exit places");
        }

        const race = compile(raceModel());
        const hot = race[1];
        if (hot.enabledBefore.slice().sort().join() !== "read,write") throw new Error("race enabling");
        const writeInputs = Object.keys(raceModel().transitions.write.inputs);
        const readInputs = Object.keys(raceModel().transitions.read.inputs);
        if (writeInputs.concat(readInputs).indexOf("L") !== -1) throw new Error("L must not be a place");

        const expect = {
            AV1: ["Load:i", "Store:j", "Store:i"],
            AV2: ["Store:i", "Store:j", "Load:i"],
            AV3: ["Load:i", "Store:j", "Load:i"]
        };
        Object.keys(expect).forEach(function (kind) {
            const steps = compile(atomicityModel(kind));
            const got = steps[steps.length - 1].trace.map(function (event) {
                return event.kind + ":" + event.tid;
            });
            if (got.join() !== expect[kind].join()) {
                throw new Error(kind + " trace " + got.join(" "));
            }
            const mid = steps[steps.length - 1].trace[1];
            const start = steps[steps.length - 1].trace[0];
            if (mid.tid === start.tid || mid.alias !== start.alias || mid.kind !== "Store") {
                throw new Error(kind + " mid event");
            }
        });
    }

    function el(name, attrs) {
        const node = document.createElementNS("http://www.w3.org/2000/svg", name);
        Object.keys(attrs || {}).forEach(function (key) {
            node.setAttribute(key, attrs[key]);
        });
        return node;
    }

    function boxOf(model, id) {
        const place = model.places[id];
        if (place) return { kind: "place", x: place.x, y: place.y, r: place.r || 26 };
        const transition = model.transitions[id];
        return { kind: "trans", x: transition.x, y: transition.y, hw: 8, hh: 28 };
    }

    function rimPoint(box, tx, ty) {
        const dx = tx - box.x;
        const dy = ty - box.y;
        if (box.kind === "place") {
            const len = Math.hypot(dx, dy) || 1;
            return { x: box.x + (dx / len) * (box.r + 2), y: box.y + (dy / len) * (box.r + 2) };
        }
        const scale = Math.min(box.hw / Math.abs(dx || 1e-6), box.hh / Math.abs(dy || 1e-6));
        return { x: box.x + dx * scale, y: box.y + dy * scale };
    }

    function arcPath(fromBox, toBox, bend) {
        const mx = (fromBox.x + toBox.x) / 2;
        const my = (fromBox.y + toBox.y) / 2;
        const dx = toBox.x - fromBox.x;
        const dy = toBox.y - fromBox.y;
        const len = Math.hypot(dx, dy) || 1;
        const cx = mx + (-dy / len) * (bend || 0);
        const cy = my + (dx / len) * (bend || 0);
        const p1 = rimPoint(fromBox, bend ? cx : toBox.x, bend ? cy : toBox.y);
        const p2 = rimPoint(toBox, bend ? cx : fromBox.x, bend ? cy : fromBox.y);
        if (!bend) {
            return "M " + p1.x.toFixed(1) + " " + p1.y.toFixed(1) + " L " + p2.x.toFixed(1) + " " + p2.y.toFixed(1);
        }
        return "M " + p1.x.toFixed(1) + " " + p1.y.toFixed(1) +
            " Q " + cx.toFixed(1) + " " + cy.toFixed(1) +
            " " + p2.x.toFixed(1) + " " + p2.y.toFixed(1);
    }

    function mountNet(root, model, options) {
        const allowAutoplay = !options || options.autoplay !== false;
        const steps = compile(model);
        root.innerHTML = "";
        const stage = document.createElement("div");
        stage.className = "stage";
        const frame = document.createElement("div");
        frame.className = "frame";
        const svg = el("svg", { viewBox: model.viewBox, role: "img" });
        svg.setAttribute("aria-label", model.label);
        const markerId = "arrow-" + model.id;
        const defs = el("defs");
        const marker = el("marker", {
            id: markerId, viewBox: "0 0 8 8", markerWidth: "8", markerHeight: "8",
            refX: "7", refY: "4", orient: "auto"
        });
        marker.appendChild(el("path", { d: "M0,0 L8,4 L0,8 Z", fill: "#1b3350" }));
        defs.appendChild(marker);
        ["A", "B"].forEach(function (name, index) {
            const colored = el("marker", {
                id: markerId + "-" + name, viewBox: "0 0 8 8", markerWidth: "8", markerHeight: "8",
                refX: "7", refY: "4", orient: "auto"
            });
            colored.appendChild(el("path", { d: "M0,0 L8,4 L0,8 Z", fill: index === 0 ? "#0e6b62" : "#8a6a32" }));
            defs.appendChild(colored);
        });
        svg.appendChild(defs);

        (model.bands || []).forEach(function (band) {
            svg.appendChild(el("rect", {
                x: band.x, y: band.y, width: band.w, height: band.h, rx: 16, class: band.cls
            }));
        });

        const arcs = [];
        Object.keys(model.transitions).forEach(function (id) {
            const transition = model.transitions[id];
            Object.keys(transition.inputs).forEach(function (placeId) {
                arcs.push({ from: placeId, to: id, key: placeId + "->" + id });
            });
            Object.keys(transition.outputs).forEach(function (placeId) {
                arcs.push({ from: id, to: placeId, key: id + "->" + placeId });
            });
        });
        const arcNodes = {};
        arcs.forEach(function (arc) {
            const resource = arc.from === "A" || arc.from === "B" ? arc.from : "";
            const path = el("path", {
                d: arcPath(boxOf(model, arc.from), boxOf(model, arc.to), model.bends[arc.key] || 0),
                class: "arc" + (resource ? " res-" + resource : ""),
                "marker-end": "url(#" + markerId + (resource ? "-" + resource : "") + ")"
            });
            path.dataset.key = arc.key;
            svg.appendChild(path);
            arcNodes[arc.key] = path;
        });

        if (model.chip) {
            const chip = model.chip;
            svg.appendChild(el("rect", {
                x: chip.x - chip.w / 2, y: chip.y - chip.h / 2,
                width: chip.w, height: chip.h, rx: 16, class: "chip"
            }));
            const text = el("text", {
                x: chip.x, y: chip.y + 4, "text-anchor": "middle", class: "chip-text"
            });
            text.textContent = chip.text;
            svg.appendChild(text);
        }

        const placeNodes = {};
        Object.keys(model.places).forEach(function (id) {
            const place = model.places[id];
            const group = el("g", { class: "place" });
            const circle = el("circle", {
                cx: place.x, cy: place.y, r: place.r || 26,
                class: "place-shape" + (place.resource ? " resource" : "") + (place.ghost ? " ghost" : "")
            });
            group.appendChild(circle);
            const label = el("text", {
                x: place.x, y: place.y + (place.r || 26) + 16,
                "text-anchor": "middle",
                class: place.ghost ? "ghost-label" : "plabel"
            });
            label.textContent = place.label;
            group.appendChild(label);
            svg.appendChild(group);
            placeNodes[id] = group;
        });

        const transNodes = {};
        Object.keys(model.transitions).forEach(function (id) {
            const transition = model.transitions[id];
            const group = el("g", { class: "trans" });
            group.appendChild(el("rect", {
                x: transition.x - 8, y: transition.y - 28, width: 16, height: 56, rx: 3, class: "trans-shape"
            }));
            const label = el("text", {
                x: transition.x, y: transition.y - 38, "text-anchor": "middle", class: "tlabel"
            });
            label.textContent = transition.label;
            group.appendChild(label);
            if (transition.sub) {
                const sub = el("text", {
                    x: transition.x, y: transition.y + 48, "text-anchor": "middle", class: "tsub"
                });
                sub.textContent = transition.sub;
                group.appendChild(sub);
            }
            svg.appendChild(group);
            transNodes[id] = group;
        });

        frame.appendChild(svg);

        const readout = document.createElement("aside");
        readout.className = "readout";
        const kicker = document.createElement("p");
        kicker.className = "step-kicker";
        const title = document.createElement("h3");
        const caption = document.createElement("p");
        caption.className = "caption";
        const inset = document.createElement("pre");
        inset.className = "inset";
        readout.append(kicker, title, caption, inset);

        stage.append(frame, readout);

        const controls = document.createElement("div");
        controls.className = "controls";
        function button(action, text) {
            const node = document.createElement("button");
            node.type = "button";
            node.dataset.act = action;
            node.textContent = text;
            return node;
        }
        const prev = button("prev", "Back");
        const play = button("play", "Play");
        play.setAttribute("aria-pressed", "false");
        const next = button("next", "Next");
        const reset = button("reset", "Reset");
        const dots = document.createElement("div");
        dots.className = "dots";
        const dotButtons = steps.map(function (_, index) {
            const dot = document.createElement("button");
            dot.type = "button";
            dot.dataset.act = "goto";
            dot.dataset.index = String(index);
            dot.textContent = String(index + 1);
            dot.setAttribute("aria-label", "Step " + (index + 1));
            dots.appendChild(dot);
            return dot;
        });
        controls.append(prev, play, next, reset, dots);
        root.append(stage, controls);

        let index = 0;
        let timer = null;
        let playing = false;
        const reduced = window.matchMedia("(prefers-reduced-motion: reduce)").matches;

        function tokenGroup(placeId, count, animate) {
            const place = model.places[placeId];
            const existing = placeNodes[placeId].querySelector(".tokens");
            if (existing) existing.remove();
            const zero = placeNodes[placeId].querySelector(".zero");
            if (zero) zero.remove();
            if (count <= 0) {
                if (place.ghost) {
                    const text = el("text", {
                        x: place.x, y: place.y + 4, "text-anchor": "middle", class: "zero"
                    });
                    text.textContent = "0";
                    placeNodes[placeId].appendChild(text);
                }
                return;
            }
            const group = el("g", { class: "tokens" });
            const circle = el("circle", { cx: place.x, cy: place.y, r: 7, class: "token" + (animate ? " in" : "") });
            group.appendChild(circle);
            placeNodes[placeId].appendChild(group);
        }

        function render(animate) {
            const step = steps[index];
            root.dataset.step = String(index);
            root.dataset.stepId = step.title;
            kicker.textContent = "Step " + (index + 1) + " of " + steps.length;
            title.textContent = step.title;
            caption.textContent = step.body;
            let insetText = step.inset;
            if (model.kind && step.trace.length) {
                const lines = step.trace.map(function (event, eventIndex) {
                    const role = event.role ? "  " + event.role : "";
                    return (eventIndex + 1) + ". " + event.kind + "  thread " + event.tid + role;
                });
                if (step.witness) lines.push("→ " + model.kind);
                insetText = lines.join("\n");
            }
            inset.textContent = insetText;
            readout.className = "readout" + (step.stuck ? " stuck" : step.race ? " race" : step.witness ? " atom" : "");
            prev.disabled = index === 0;
            next.disabled = index === steps.length - 1;
            dotButtons.forEach(function (dot, dotIndex) {
                if (dotIndex === index) dot.setAttribute("aria-current", "step");
                else dot.removeAttribute("aria-current");
            });

            Object.keys(model.places).forEach(function (id) {
                const grew = animate && step.after[id] > step.before[id];
                tokenGroup(id, step.after[id], grew);
                const shape = placeNodes[id].querySelector(".place-shape");
                shape.classList.toggle("noted", step.notePlaces.indexOf(id) !== -1);
            });

            Object.keys(arcNodes).forEach(function (key) {
                arcNodes[key].classList.remove("hot", "flow");
            });
            Object.keys(transNodes).forEach(function (id) {
                const node = transNodes[id];
                node.classList.remove("enabled", "firing", "waiting");
                const enabled = step.showEnabled && step.enabledAfter.indexOf(id) !== -1;
                if (enabled) node.classList.add("enabled");
                if (step.waiting.indexOf(id) !== -1) node.classList.add("waiting");
                if (animate && step.fire === id) {
                    node.classList.add("firing");
                    const transition = model.transitions[id];
                    Object.keys(transition.inputs).forEach(function (placeId) {
                        const path = arcNodes[placeId + "->" + id];
                        if (path) path.classList.add("flow");
                    });
                    Object.keys(transition.outputs).forEach(function (placeId) {
                        const path = arcNodes[id + "->" + placeId];
                        if (path) path.classList.add("flow");
                    });
                }
            });
            if (step.race) {
                Object.keys(transNodes).forEach(function (id) {
                    if (step.enabledAfter.indexOf(id) !== -1) transNodes[id].classList.add("enabled");
                });
            }
            svg.setAttribute("aria-label", model.label + ". " + step.title + ". " + step.body);
        }

        function clearTimer() {
            if (timer) clearTimeout(timer);
            timer = null;
        }

        function pause() {
            playing = false;
            play.setAttribute("aria-pressed", "false");
            play.textContent = "Play";
            clearTimer();
        }

        function schedule() {
            clearTimer();
            if (!playing) return;
            const delay = index === steps.length - 1 ? 3400 : 2300;
            timer = setTimeout(function () {
                go(index === steps.length - 1 ? 0 : index + 1, true);
                schedule();
            }, delay);
        }

        function playFromHere() {
            playing = true;
            play.setAttribute("aria-pressed", "true");
            play.textContent = "Pause";
            schedule();
        }

        function go(nextIndex, animate) {
            index = nextIndex;
            render(Boolean(animate));
        }

        controls.addEventListener("click", function (event) {
            const target = event.target.closest("button");
            if (!target) return;
            const action = target.dataset.act;
            if (action === "play") {
                if (playing) pause();
                else playFromHere();
                return;
            }
            pause();
            if (action === "next" && index < steps.length - 1) go(index + 1, true);
            if (action === "prev" && index > 0) go(index - 1, false);
            if (action === "reset") go(0, false);
            if (action === "goto") go(Number(target.dataset.index), false);
        });

        go(0, false);

        let started = false;
        if (allowAutoplay && !reduced && "IntersectionObserver" in window) {
            const observer = new IntersectionObserver(function (entries) {
                if (entries[0].isIntersecting && !started) {
                    started = true;
                    playFromHere();
                } else if (!entries[0].isIntersecting && playing) {
                    pause();
                }
            }, { threshold: 0.45 });
            observer.observe(root);
        }

        return {
            go: function (nextIndex) { pause(); go(nextIndex, false); },
            last: function () { pause(); go(steps.length - 1, false); },
            pause: pause,
            length: steps.length
        };
    }

    const PIPELINE = [
        {
            name: "MIR",
            text: "pn is a rustc driver. After analysis, PTACallbacks collects monomorphized function instances from the codegen units. That is the MIR this run will translate."
        },
        {
            name: "Call graph",
            text: "CallGraph::analyze walks those instances and the configured concurrency APIs. The graph says which functions to translate. With --viz-callgraph the callback writes callgraph.dot."
        },
        {
            name: "Petri net",
            text: "PetriNet::construct builds function places, locks, channels, atomics, and unsafe accesses, then translates each reachable MIR body. The net before reduction can be written as petrinet_raw.dot."
        },
        {
            name: "Reduce",
            text: "Reduction is on unless --no-reduce is set. unipn's reduce_in_place simplifies loops, then sequences, then intermediate places. The three stage files are petrinet_reduce_1_loop.dot, petrinet_reduce_2_sequence.dot, and petrinet_reduce_3_intermediate.dot. The net used next is petrinet.dot."
        },
        {
            name: "State graph",
            text: "StateGraph::with_config explores markings of that net. Each node is a marking. Each edge is one enabled transition firing. --por turns on partial-order reduction. A state limit can stop the exploration early. The drawing is stategraph.dot."
        },
        {
            name: "Detectors",
            text: "run_detectors reads that state graph. The default mode is deadlock. --mode datarace and --mode atomic select the other two. --mode all runs deadlock and data race together; atomicity stays on --mode atomic. Reports are deadlock_report.txt, datarace_report.txt, or atomicity_report.txt."
        }
    ];

    const ARCH = [
        {
            name: "Driver",
            path: "src/bin/pn.rs · src/callback.rs",
            text: "src/bin/pn.rs calls conc_bug_detector::run. src/callback.rs owns the order: MIR, call graph, Petri net, optional reduction, state graph, then the detector for the selected mode."
        },
        {
            name: "Translation",
            path: "src/translate/",
            text: "src/translate/callgraph.rs builds the call graph. src/translate/petri_net.rs is PetriNet::construct and uses unipn's PtBuilder. src/translate/mir_to_pn/ turns MIR bodies into places and transitions, including Lock, Unlock, and unsafe accesses."
        },
        {
            name: "Alias identity",
            path: "src/memory/",
            branch: true,
            text: "While the net is built, src/memory/ chooses the alias ids later detectors treat as one location. Data race and atomicity do not rediscover which pointers alias. This is not a fourth bug detector. --mode pointsto can stop after that information."
        },
        {
            name: "Net library",
            path: "unipn",
            text: "Place, transition, and marking types come from the unipn crate pinned in Cargo.toml. Reduction is unipn::analysis::pt::reduce::reduce_in_place. The state graph is unipn::analysis::pt::reachability::StateGraph. There is no src/net directory and no src/analysis directory in this repo."
        },
        {
            name: "Detectors",
            path: "src/detect/",
            text: "src/detect/deadlock.rs, datarace.rs, and atomicity_violation.rs read the state graph. src/report/ holds the report structs. The callback writes the text and JSON files. Detectors do not rebuild the net."
        }
    ];

    function mountChoice(root, items, renderItem) {
        root.innerHTML = "";
        const list = document.createElement("div");
        const panel = document.createElement("aside");
        panel.className = "readout";
        const kicker = document.createElement("p");
        kicker.className = "step-kicker";
        const title = document.createElement("h3");
        const body = document.createElement("p");
        body.className = "caption";
        panel.append(kicker, title, body);
        const buttons = items.map(function (item, index) {
            const button = renderItem(item, index);
            button.type = "button";
            button.dataset.index = String(index);
            list.appendChild(button);
            return button;
        });
        const controls = document.createElement("div");
        controls.className = "controls";
        const prev = document.createElement("button");
        prev.type = "button";
        prev.textContent = "Back";
        const play = document.createElement("button");
        play.type = "button";
        play.textContent = "Play";
        play.setAttribute("aria-pressed", "false");
        const next = document.createElement("button");
        next.type = "button";
        next.textContent = "Next";
        controls.append(prev, play, next);
        root.append(list, panel, controls);

        let index = 0;
        let timer = null;
        let playing = false;

        function show() {
            const item = items[index];
            kicker.textContent = "Step " + (index + 1) + " of " + items.length;
            title.textContent = item.name;
            body.textContent = item.text;
            buttons.forEach(function (button, buttonIndex) {
                if (buttonIndex === index) button.setAttribute("aria-current", "step");
                else button.removeAttribute("aria-current");
            });
            prev.disabled = index === 0;
            next.disabled = index === items.length - 1;
            root.dataset.step = String(index);
        }

        function pause() {
            playing = false;
            play.setAttribute("aria-pressed", "false");
            play.textContent = "Play";
            if (timer) clearTimeout(timer);
            timer = null;
        }

        function schedule() {
            if (timer) clearTimeout(timer);
            if (!playing) return;
            timer = setTimeout(function () {
                index = index === items.length - 1 ? 0 : index + 1;
                show();
                schedule();
            }, 2600);
        }

        controls.addEventListener("click", function (event) {
            if (event.target === play) {
                if (playing) pause();
                else {
                    playing = true;
                    play.setAttribute("aria-pressed", "true");
                    play.textContent = "Pause";
                    schedule();
                }
                return;
            }
            pause();
            if (event.target === next && index < items.length - 1) index += 1;
            if (event.target === prev && index > 0) index -= 1;
            show();
        });
        list.addEventListener("click", function (event) {
            const button = event.target.closest("button");
            if (!button) return;
            pause();
            index = Number(button.dataset.index);
            show();
        });
        show();

        const reduced = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
        if (!reduced && "IntersectionObserver" in window) {
            let started = false;
            const observer = new IntersectionObserver(function (entries) {
                if (entries[0].isIntersecting && !started) {
                    started = true;
                    playing = true;
                    play.setAttribute("aria-pressed", "true");
                    play.textContent = "Pause";
                    schedule();
                } else if (!entries[0].isIntersecting) {
                    pause();
                }
            }, { threshold: 0.5 });
            observer.observe(root);
        }
        return {
            go: function (nextIndex) { pause(); index = nextIndex; show(); }
        };
    }

    const players = {};

    function boot() {
        selfCheck();
        players.firing = mountNet(document.getElementById("plate-firing"), firingModel());
        players.deadlock = mountNet(document.getElementById("plate-deadlock"), deadlockModel());
        players.race = mountNet(document.getElementById("plate-race"), raceModel());

        const atomRoot = document.getElementById("plate-atom");
        let atomKind = "AV1";
        function mountAtom(autoplay) {
            players.atom = mountNet(atomRoot, atomicityModel(atomKind), { autoplay: autoplay !== false });
        }
        mountAtom();
        document.getElementById("av-switch").addEventListener("click", function (event) {
            const button = event.target.closest("button");
            if (!button) return;
            atomKind = button.dataset.av;
            document.querySelectorAll("#av-switch button").forEach(function (node) {
                node.setAttribute("aria-selected", node === button ? "true" : "false");
            });
            mountAtom();
        });

        mountChoice(document.getElementById("plate-pipeline"), PIPELINE, function (item, index) {
            const button = document.createElement("button");
            button.className = "pipe";
            button.innerHTML = "<small>0" + (index + 1) + "</small><strong>" + item.name + "</strong>";
            return button;
        });
        const pipeline = document.getElementById("plate-pipeline");
        const pipes = pipeline.querySelector("div");
        pipes.className = "pipeline";

        mountChoice(document.getElementById("plate-arch"), ARCH, function (item) {
            const button = document.createElement("button");
            button.className = "node" + (item.branch ? " branch" : "");
            button.innerHTML = "<b>" + item.name + "</b><span>" + item.path + "</span>";
            return button;
        });
        const arch = document.getElementById("plate-arch");
        arch.querySelector("div").className = "arch";

        document.getElementById("outcomes").addEventListener("click", function (event) {
            const button = event.target.closest("button");
            if (!button) return;
            const id = button.dataset.replay;
            const target = document.getElementById(button.dataset.target);
            if (id === "atom" && button.dataset.av) {
                atomKind = button.dataset.av;
                document.querySelectorAll("#av-switch button").forEach(function (node) {
                    node.setAttribute("aria-selected", node.dataset.av === atomKind ? "true" : "false");
                });
                mountAtom(false);
            }
            target.scrollIntoView({ behavior: "smooth", block: "center" });
            players[id].last();
        });
    }

    const api = {
        compile: compile,
        firingModel: firingModel,
        deadlockModel: deadlockModel,
        raceModel: raceModel,
        atomicityModel: atomicityModel,
        selfCheck: selfCheck
    };

    if (typeof module !== "undefined" && module.exports) module.exports = api;
    if (typeof document !== "undefined") {
        if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", boot);
        else boot();
    }
})();
