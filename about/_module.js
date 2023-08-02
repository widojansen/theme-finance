function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.59.1 */

function create_fragment(ctx) {
	let style;
	let t;

	return {
		c() {
			style = element("style");
			t = text("/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: #20bfa9;\n  --color-accent-2: #ff794d;\n\n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #e1ecf0;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: #1d263a;\n  line-height: 1.2;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1250px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n  font-weight: 500;\n  border-bottom: 2px solid;\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.1;\n  font-weight: 600;\n}\n\n.subheading {\n  font-weight: 400;\n  line-height: 1.5;\n  opacity: 90%;\n}\n\n.button {\n  display: inline-flex;\n  align-items: center;\n  justify-content: center;\n  gap: 0.5rem;\n  color: white;\n  font-weight: 500;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 3rem;\n  padding: 15px 25px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.section .content {\n  max-width: 1200px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n.section .content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n  }\n.section .content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.section .content a.link {\n  }\n.section .content h1 {\n    font-size: 3rem;\n    font-weight: 700;\n    margin-bottom: 1rem;\n  }\n.section .content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n.section .content h3 {\n    font-size: 1.75rem;\n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n.section .content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }");
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1vsfxrb', document.head);
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: #20bfa9;\n  --color-accent-2: #ff794d;\n\n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #e1ecf0;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: #1d263a;\n  line-height: 1.2;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1250px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n  font-weight: 500;\n  border-bottom: 2px solid;\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.1;\n  font-weight: 600;\n}\n\n.subheading {\n  font-weight: 400;\n  line-height: 1.5;\n  opacity: 90%;\n}\n\n.button {\n  display: inline-flex;\n  align-items: center;\n  justify-content: center;\n  gap: 0.5rem;\n  color: white;\n  font-weight: 500;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 3rem;\n  padding: 15px 25px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.section .content {\n  max-width: 1200px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n.section .content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n  }\n.section .content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.section .content a.link {\n  }\n.section .content h1 {\n    font-size: 3rem;\n    font-weight: 700;\n    margin-bottom: 1rem;\n  }\n.section .content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n.section .content h3 {\n    font-size: 1.75rem;\n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n.section .content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
		},
		m(target, anchor) {
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(2, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(3, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(4, company_description = $$props.company_description);
	};

	return [logo, site_nav, primary_cta, footer_links, company_description];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			logo: 0,
			site_nav: 1,
			primary_cta: 2,
			footer_links: 3,
			company_description: 4
		});
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.59.1 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

// (111:31) 
function create_if_block_4(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (109:6) {#if logo.title}
function create_if_block_3(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (116:6) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-qh80cp");
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (126:31) 
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (124:6) {#if logo.title}
function create_if_block_1$1(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (136:4) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let t0;
	let a;
	let t1_value = /*primary_cta*/ ctx[2].label + "";
	let t1;
	let a_href_value;
	let t2;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			a = element("a");
			t1 = text(t1_value);
			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t0 = claim_space(nav_nodes);
			a = claim_element(nav_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t1 = claim_text(a_nodes, t1_value);
			a_nodes.forEach(detach);
			t2 = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*primary_cta*/ ctx[2].url);
			attr(a, "class", "button svelte-qh80cp");
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-qh80cp");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-qh80cp");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t0);
			append_hydration(nav, a);
			append_hydration(a, t1);
			append_hydration(nav, t2);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[7]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2) {
				each_value = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t0);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if ((!current || dirty & /*primary_cta*/ 4) && t1_value !== (t1_value = /*primary_cta*/ ctx[2].label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*primary_cta*/ 4 && a_href_value !== (a_href_value = /*primary_cta*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (138:8) {#each site_nav as { link }}
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$2(ctx) {
	let div2;
	let header;
	let div0;
	let a0;
	let t0;
	let nav;
	let t1;
	let a1;
	let t2_value = /*primary_cta*/ ctx[2].label + "";
	let t2;
	let a1_href_value;
	let t3;
	let div1;
	let a2;
	let t4;
	let button;
	let icon;
	let t5;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_3;
		if (/*logo*/ ctx[0].image.url) return create_if_block_4;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type && current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_1$1;
		if (/*logo*/ ctx[0].image.url) return create_if_block_2;
	}

	let current_block_type_1 = select_block_type_1(ctx);
	let if_block1 = current_block_type_1 && current_block_type_1(ctx);

	icon = new Component$1({
			props: { height: "30", icon: "eva:menu-outline" }
		});

	let if_block2 = /*mobileNavOpen*/ ctx[3] && create_if_block$1(ctx);

	return {
		c() {
			div2 = element("div");
			header = element("header");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			a1 = element("a");
			t2 = text(t2_value);
			t3 = space();
			div1 = element("div");
			a2 = element("a");
			if (if_block1) if_block1.c();
			t4 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t5 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t1 = claim_space(nav_nodes);
			a1 = claim_element(nav_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			t2 = claim_text(a1_nodes, t2_value);
			a1_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a2 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a2_nodes = children(a2);
			if (if_block1) if_block1.l(a2_nodes);
			a2_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t5 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-qh80cp");
			attr(a1, "href", a1_href_value = /*primary_cta*/ ctx[2].url);
			attr(a1, "class", "button svelte-qh80cp");
			attr(nav, "class", "svelte-qh80cp");
			attr(div0, "class", "desktop-nav svelte-qh80cp");
			attr(a2, "href", "/");
			attr(a2, "class", "logo svelte-qh80cp");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-qh80cp");
			attr(header, "class", "section-container svelte-qh80cp");
			attr(div2, "class", "section");
			attr(div2, "id", "section-e6304854");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, header);
			append_hydration(header, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t1);
			append_hydration(nav, a1);
			append_hydration(a1, t2);
			append_hydration(header, t3);
			append_hydration(header, div1);
			append_hydration(div1, a2);
			if (if_block1) if_block1.m(a2, null);
			append_hydration(div1, t4);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t5);
			if (if_block2) if_block2.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[6]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if (if_block0) if_block0.d(1);
				if_block0 = current_block_type && current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a0, null);
				}
			}

			if (dirty & /*site_nav*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t1);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if ((!current || dirty & /*primary_cta*/ 4) && t2_value !== (t2_value = /*primary_cta*/ ctx[2].label + "")) set_data(t2, t2_value);

			if (!current || dirty & /*primary_cta*/ 4 && a1_href_value !== (a1_href_value = /*primary_cta*/ ctx[2].url)) {
				attr(a1, "href", a1_href_value);
			}

			if (current_block_type_1 === (current_block_type_1 = select_block_type_1(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if (if_block1) if_block1.d(1);
				if_block1 = current_block_type_1 && current_block_type_1(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(a2, null);
				}
			}

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$1(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);

			if (if_block0) {
				if_block0.d();
			}

			destroy_each(each_blocks, detaching);

			if (if_block1) {
				if_block1.d();
			}

			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(3, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(3, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(2, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(4, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(5, company_description = $$props.company_description);
	};

	return [
		logo,
		site_nav,
		primary_cta,
		mobileNavOpen,
		footer_links,
		company_description,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			logo: 0,
			site_nav: 1,
			primary_cta: 2,
			footer_links: 4,
			company_description: 5
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$3(ctx) {
	let div1;
	let section;
	let div0;
	let h1;
	let t0;
	let t1;
	let h3;
	let t2;
	let t3;
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			h1 = element("h1");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			h3 = element("h3");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			img = element("img");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h1 = claim_element(div0_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t0 = claim_text(h1_nodes, /*heading*/ ctx[0]);
			h1_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t2 = claim_text(h3_nodes, /*subheading*/ ctx[1]);
			h3_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			img = claim_element(section_nodes, "IMG", { class: true, src: true, alt: true });
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "heading svelte-10q5o6o");
			attr(h3, "class", "subheading");
			attr(div0, "class", "main svelte-10q5o6o");
			attr(img, "class", "image svelte-10q5o6o");
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[2].alt);
			attr(section, "class", "section-container svelte-10q5o6o");
			attr(div1, "class", "section");
			attr(div1, "id", "section-ef5bb9cf");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, div0);
			append_hydration(div0, h1);
			append_hydration(h1, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h3);
			append_hydration(h3, t2);
			append_hydration(section, t3);
			append_hydration(section, img);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);

			if (dirty & /*image*/ 4 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 4 && img_alt_value !== (img_alt_value = /*image*/ ctx[2].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { image } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(3, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(4, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(5, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(6, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(7, company_description = $$props.company_description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('image' in $$props) $$invalidate(2, image = $$props.image);
	};

	return [
		heading,
		subheading,
		image,
		logo,
		site_nav,
		primary_cta,
		footer_links,
		company_description
	];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			logo: 3,
			site_nav: 4,
			primary_cta: 5,
			footer_links: 6,
			company_description: 7,
			heading: 0,
			subheading: 1,
			image: 2
		});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i].icon;
	child_ctx[7] = list[i].description;
	return child_ctx;
}

// (40:4) {#each icon_list as { icon, description }}
function create_each_block$1(ctx) {
	let li;
	let div0;
	let icon;
	let t0;
	let div1;
	let t1_value = /*description*/ ctx[7] + "";
	let t1;
	let t2;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[6] } });

	return {
		c() {
			li = element("li");
			div0 = element("div");
			create_component(icon.$$.fragment);
			t0 = space();
			div1 = element("div");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			div0 = claim_element(li_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			claim_component(icon.$$.fragment, div0_nodes);
			div0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			div1 = claim_element(li_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			t1 = claim_text(div1_nodes, t1_value);
			div1_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "icon svelte-1hues2b");
			attr(div1, "class", "description svelte-1hues2b");
			attr(li, "class", "svelte-1hues2b");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, div0);
			mount_component(icon, div0, null);
			append_hydration(li, t0);
			append_hydration(li, div1);
			append_hydration(div1, t1);
			append_hydration(li, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*icon_list*/ 1) icon_changes.icon = /*icon*/ ctx[6];
			icon.$set(icon_changes);
			if ((!current || dirty & /*icon_list*/ 1) && t1_value !== (t1_value = /*description*/ ctx[7] + "")) set_data(t1, t1_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$4(ctx) {
	let div;
	let section;
	let ul;
	let current;
	let each_value = /*icon_list*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div = element("div");
			section = element("section");
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			section = claim_element(div_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(ul, "class", "svelte-1hues2b");
			attr(section, "class", "section-container svelte-1hues2b");
			attr(div, "class", "section");
			attr(div, "id", "section-09cf3108");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, section);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (dirty & /*icon_list*/ 1) {
				each_value = /*icon_list*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;
	let { icon_list } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(1, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(2, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(3, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(4, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(5, company_description = $$props.company_description);
		if ('icon_list' in $$props) $$invalidate(0, icon_list = $$props.icon_list);
	};

	return [icon_list, logo, site_nav, primary_cta, footer_links, company_description];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			logo: 1,
			site_nav: 2,
			primary_cta: 3,
			footer_links: 4,
			company_description: 5,
			icon_list: 0
		});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i];
	return child_ctx;
}

// (73:6) {#each items as item}
function create_each_block$2(ctx) {
	let li;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let div0;
	let t1_value = /*item*/ ctx[7].title + "";
	let t1;
	let t2;
	let div1;
	let t3_value = /*item*/ ctx[7].subtitle + "";
	let t3;
	let t4;
	let div2;
	let raw_value = /*item*/ ctx[7].description.html + "";
	let t5;

	return {
		c() {
			li = element("li");
			img = element("img");
			t0 = space();
			div0 = element("div");
			t1 = text(t1_value);
			t2 = space();
			div1 = element("div");
			t3 = text(t3_value);
			t4 = space();
			div2 = element("div");
			t5 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			img = claim_element(li_nodes, "IMG", { src: true, alt: true, class: true });
			t0 = claim_space(li_nodes);
			div0 = claim_element(li_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			t1 = claim_text(div0_nodes, t1_value);
			div0_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			div1 = claim_element(li_nodes, "DIV", {});
			var div1_nodes = children(div1);
			t3 = claim_text(div1_nodes, t3_value);
			div1_nodes.forEach(detach);
			t4 = claim_space(li_nodes);
			div2 = claim_element(li_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div2_nodes.forEach(detach);
			t5 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*item*/ ctx[7].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*item*/ ctx[7].image.alt);
			attr(img, "class", "svelte-1a45id5");
			attr(div0, "class", "title svelte-1a45id5");
			attr(div2, "class", "description svelte-1a45id5");
			attr(li, "class", "svelte-1a45id5");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, img);
			append_hydration(li, t0);
			append_hydration(li, div0);
			append_hydration(div0, t1);
			append_hydration(li, t2);
			append_hydration(li, div1);
			append_hydration(div1, t3);
			append_hydration(li, t4);
			append_hydration(li, div2);
			div2.innerHTML = raw_value;
			append_hydration(li, t5);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 2 && !src_url_equal(img.src, img_src_value = /*item*/ ctx[7].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*items*/ 2 && img_alt_value !== (img_alt_value = /*item*/ ctx[7].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*items*/ 2 && t1_value !== (t1_value = /*item*/ ctx[7].title + "")) set_data(t1, t1_value);
			if (dirty & /*items*/ 2 && t3_value !== (t3_value = /*item*/ ctx[7].subtitle + "")) set_data(t3, t3_value);
			if (dirty & /*items*/ 2 && raw_value !== (raw_value = /*item*/ ctx[7].description.html + "")) div2.innerHTML = raw_value;		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

function create_fragment$5(ctx) {
	let div1;
	let section;
	let div0;
	let h2;
	let t0;
	let t1;
	let ul;
	let each_value = /*items*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			ul = claim_element(div0_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-1a45id5");
			attr(ul, "class", "svelte-1a45id5");
			attr(div0, "class", "section-container svelte-1a45id5");
			attr(section, "class", "svelte-1a45id5");
			attr(div1, "class", "section");
			attr(div1, "id", "section-26c510b1");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			append_hydration(div0, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*items*/ 2) {
				each_value = /*items*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;
	let { heading } = $$props;
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(2, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(3, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(4, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(5, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(6, company_description = $$props.company_description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('items' in $$props) $$invalidate(1, items = $$props.items);
	};

	return [heading, items, logo, site_nav, primary_cta, footer_links, company_description];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			logo: 2,
			site_nav: 3,
			primary_cta: 4,
			footer_links: 5,
			company_description: 6,
			heading: 0,
			items: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context$3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i].label;
	child_ctx[6] = list[i].link_list;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

// (100:31) 
function create_if_block_1$2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (98:6) {#if logo.title}
function create_if_block$2(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (111:10) {#each link_list as { link }}
function create_each_block_1$1(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-gkcc88");
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*footer_links*/ 2 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*footer_links*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (107:4) {#each footer_links as { label, link_list }}
function create_each_block$3(ctx) {
	let div;
	let h4;
	let t0_value = /*label*/ ctx[5] + "";
	let t0;
	let t1;
	let nav;
	let t2;
	let each_value_1 = /*link_list*/ ctx[6];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	return {
		c() {
			div = element("div");
			h4 = element("h4");
			t0 = text(t0_value);
			t1 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			h4 = claim_element(div_nodes, "H4", { class: true });
			var h4_nodes = children(h4);
			t0 = claim_text(h4_nodes, t0_value);
			h4_nodes.forEach(detach);
			t1 = claim_space(div_nodes);
			nav = claim_element(div_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			t2 = claim_space(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h4, "class", "label svelte-gkcc88");
			attr(nav, "class", "svelte-gkcc88");
			attr(div, "class", "item svelte-gkcc88");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, h4);
			append_hydration(h4, t0);
			append_hydration(div, t1);
			append_hydration(div, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(div, t2);
		},
		p(ctx, dirty) {
			if (dirty & /*footer_links*/ 2 && t0_value !== (t0_value = /*label*/ ctx[5] + "")) set_data(t0, t0_value);

			if (dirty & /*footer_links*/ 2) {
				each_value_1 = /*link_list*/ ctx[6];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function create_fragment$6(ctx) {
	let div4;
	let footer;
	let div1;
	let a0;
	let t0;
	let div0;
	let raw_value = /*company_description*/ ctx[2].html + "";
	let t1;
	let div2;
	let t2;
	let div3;
	let span;
	let a1;
	let t3;
	let t4;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block$2;
		if (/*logo*/ ctx[0].image.url) return create_if_block_1$2;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type && current_block_type(ctx);
	let each_value = /*footer_links*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$3(get_each_context$3(ctx, each_value, i));
	}

	return {
		c() {
			div4 = element("div");
			footer = element("footer");
			div1 = element("div");
			a0 = element("a");
			if (if_block) if_block.c();
			t0 = space();
			div0 = element("div");
			t1 = space();
			div2 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			div3 = element("div");
			span = element("span");
			a1 = element("a");
			t3 = text("Primo");
			t4 = text(" Powered");
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			footer = claim_element(div4_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			div1 = claim_element(footer_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a0 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block) if_block.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t1 = claim_space(footer_nodes);
			div2 = claim_element(footer_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div2_nodes);
			}

			div2_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			t2 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			span = claim_element(div3_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			a1 = claim_element(span_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			t3 = claim_text(a1_nodes, "Primo");
			a1_nodes.forEach(detach);
			t4 = claim_text(span_nodes, " Powered");
			span_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo");
			attr(div0, "class", "company-description svelte-gkcc88");
			attr(div1, "class", "main svelte-gkcc88");
			attr(div2, "class", "links svelte-gkcc88");
			attr(footer, "class", "section-container svelte-gkcc88");
			attr(a1, "href", "https://primo.so");
			attr(a1, "class", "svelte-gkcc88");
			attr(span, "class", "primo svelte-gkcc88");
			attr(div3, "class", "subfooter svelte-gkcc88");
			attr(div4, "class", "section");
			attr(div4, "id", "section-b2f88620");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, footer);
			append_hydration(footer, div1);
			append_hydration(div1, a0);
			if (if_block) if_block.m(a0, null);
			append_hydration(div1, t0);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(footer, t1);
			append_hydration(footer, div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div2, null);
				}
			}

			append_hydration(div4, t2);
			append_hydration(div4, div3);
			append_hydration(div3, span);
			append_hydration(span, a1);
			append_hydration(a1, t3);
			append_hydration(span, t4);
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if (if_block) if_block.d(1);
				if_block = current_block_type && current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(a0, null);
				}
			}

			if (dirty & /*company_description*/ 4 && raw_value !== (raw_value = /*company_description*/ ctx[2].html + "")) div0.innerHTML = raw_value;
			if (dirty & /*footer_links*/ 2) {
				each_value = /*footer_links*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$3(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$3(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div2, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div4);

			if (if_block) {
				if_block.d();
			}

			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(3, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(4, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(1, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(2, company_description = $$props.company_description);
	};

	return [logo, footer_links, company_description, site_nav, primary_cta];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$6, safe_not_equal, {
			logo: 0,
			site_nav: 3,
			primary_cta: 4,
			footer_links: 1,
			company_description: 2
		});
	}
}

/* generated by Svelte v3.59.1 */

function instance$7($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { primary_cta } = $$props;
	let { footer_links } = $$props;
	let { company_description } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('primary_cta' in $$props) $$invalidate(2, primary_cta = $$props.primary_cta);
		if ('footer_links' in $$props) $$invalidate(3, footer_links = $$props.footer_links);
		if ('company_description' in $$props) $$invalidate(4, company_description = $$props.company_description);
	};

	return [logo, site_nav, primary_cta, footer_links, company_description];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, null, safe_not_equal, {
			logo: 0,
			site_nav: 1,
			primary_cta: 2,
			footer_links: 3,
			company_description: 4
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$7(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let current;

	component_0 = new Component({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{ "link": { "url": "/", "label": "Home" } },
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: { "url": "/", "label": "Free Consultation" },
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Global location" }
							},
							{
								"link": { "url": "/", "label": "Missions" }
							},
							{
								"link": { "url": "/", "label": "Careers" }
							},
							{
								"link": { "url": "/", "label": "Investors" }
							},
							{
								"link": { "url": "/", "label": "News rooms" }
							}
						]
					},
					{
						"label": "Impact",
						"link_list": [
							{
								"link": { "url": "/", "label": "Creator awards" }
							},
							{
								"link": { "url": "/", "label": "Creative ideas" }
							},
							{
								"link": {
									"url": "/",
									"label": "Refuge initiatives"
								}
							},
							{
								"link": { "url": "/", "label": "Residents" }
							}
						]
					},
					{
						"label": "Partnership",
						"link_list": [
							{
								"link": { "url": "/", "label": "Brokers" }
							},
							{
								"link": { "url": "/", "label": "Impact coffee" }
							},
							{
								"link": { "url": "/", "label": "Table talk" }
							},
							{
								"link": { "url": "/", "label": "Push door" }
							}
						]
					}
				],
				company_description: "<p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. In blandit tincidunt id turpis est platea sed.</p>"
			}
		});

	component_1 = new Component$2({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{
						"link": { "url": "/about", "label": "About" }
					},
					{
						"link": {
							"url": "/consultation",
							"label": "Consultation"
						}
					},
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: {
					"url": "/consultation",
					"label": "Sign up"
				},
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Global location" }
							},
							{
								"link": { "url": "/", "label": "Missions" }
							},
							{
								"link": { "url": "/", "label": "Careers" }
							},
							{
								"link": { "url": "/", "label": "Investors" }
							},
							{
								"link": { "url": "/", "label": "News rooms" }
							}
						]
					},
					{
						"label": "Impact",
						"link_list": [
							{
								"link": { "url": "/", "label": "Creator awards" }
							},
							{
								"link": { "url": "/", "label": "Creative ideas" }
							},
							{
								"link": {
									"url": "/",
									"label": "Refuge initiatives"
								}
							},
							{
								"link": { "url": "/", "label": "Residents" }
							}
						]
					},
					{
						"label": "Partnership",
						"link_list": [
							{
								"link": { "url": "/", "label": "Brokers" }
							},
							{
								"link": { "url": "/", "label": "Impact coffee" }
							},
							{
								"link": { "url": "/", "label": "Table talk" }
							},
							{
								"link": { "url": "/", "label": "Push door" }
							}
						]
					}
				],
				company_description: "<p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. In blandit tincidunt id turpis est platea sed.</p>"
			}
		});

	component_2 = new Component$3({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{ "link": { "url": "/", "label": "Home" } },
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: { "url": "/", "label": "Free Consultation" },
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Global location" }
							},
							{
								"link": { "url": "/", "label": "Missions" }
							},
							{
								"link": { "url": "/", "label": "Careers" }
							},
							{
								"link": { "url": "/", "label": "Investors" }
							},
							{
								"link": { "url": "/", "label": "News rooms" }
							}
						]
					},
					{
						"label": "Impact",
						"link_list": [
							{
								"link": { "url": "/", "label": "Creator awards" }
							},
							{
								"link": { "url": "/", "label": "Creative ideas" }
							},
							{
								"link": {
									"url": "/",
									"label": "Refuge initiatives"
								}
							},
							{
								"link": { "url": "/", "label": "Residents" }
							}
						]
					},
					{
						"label": "Partnership",
						"link_list": [
							{
								"link": { "url": "/", "label": "Brokers" }
							},
							{
								"link": { "url": "/", "label": "Impact coffee" }
							},
							{
								"link": { "url": "/", "label": "Table talk" }
							},
							{
								"link": { "url": "/", "label": "Push door" }
							}
						]
					}
				],
				company_description: "<p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. In blandit tincidunt id turpis est platea sed.</p>",
				heading: "Our Story",
				subheading: "We are an industry-leading company that values honesty, integrity, and efficiency. Building quality products and caring for the users are what made us stand out since the beginning.",
				image: {
					"alt": "",
					"url": "https://images.unsplash.com/photo-1506869640319-fe1a24fd76dc?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1770&q=80"
				}
			}
		});

	component_3 = new Component$4({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{ "link": { "url": "/", "label": "Home" } },
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: { "url": "/", "label": "Free Consultation" },
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Global location" }
							},
							{
								"link": { "url": "/", "label": "Missions" }
							},
							{
								"link": { "url": "/", "label": "Careers" }
							},
							{
								"link": { "url": "/", "label": "Investors" }
							},
							{
								"link": { "url": "/", "label": "News rooms" }
							}
						]
					},
					{
						"label": "Impact",
						"link_list": [
							{
								"link": { "url": "/", "label": "Creator awards" }
							},
							{
								"link": { "url": "/", "label": "Creative ideas" }
							},
							{
								"link": {
									"url": "/",
									"label": "Refuge initiatives"
								}
							},
							{
								"link": { "url": "/", "label": "Residents" }
							}
						]
					},
					{
						"label": "Partnership",
						"link_list": [
							{
								"link": { "url": "/", "label": "Brokers" }
							},
							{
								"link": { "url": "/", "label": "Impact coffee" }
							},
							{
								"link": { "url": "/", "label": "Table talk" }
							},
							{
								"link": { "url": "/", "label": "Push door" }
							}
						]
					}
				],
				company_description: "<p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. In blandit tincidunt id turpis est platea sed.</p>",
				icon_list: [
					{
						"icon": "material-symbols:heart-plus",
						"description": "We are an industry-leading company that values honesty, integrity, and efficiency. Building quality products and caring for the users are what made us stand out since the beginning."
					},
					{
						"icon": "material-symbols:nature-people-sharp",
						"description": "We’re a team of highly skilled professionals with years of experience in different fields vowed to revolutionize the people’s web experience."
					}
				]
			}
		});

	component_4 = new Component$5({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{ "link": { "url": "/", "label": "Home" } },
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: { "url": "/", "label": "Free Consultation" },
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Global location" }
							},
							{
								"link": { "url": "/", "label": "Missions" }
							},
							{
								"link": { "url": "/", "label": "Careers" }
							},
							{
								"link": { "url": "/", "label": "Investors" }
							},
							{
								"link": { "url": "/", "label": "News rooms" }
							}
						]
					},
					{
						"label": "Impact",
						"link_list": [
							{
								"link": { "url": "/", "label": "Creator awards" }
							},
							{
								"link": { "url": "/", "label": "Creative ideas" }
							},
							{
								"link": {
									"url": "/",
									"label": "Refuge initiatives"
								}
							},
							{
								"link": { "url": "/", "label": "Residents" }
							}
						]
					},
					{
						"label": "Partnership",
						"link_list": [
							{
								"link": { "url": "/", "label": "Brokers" }
							},
							{
								"link": { "url": "/", "label": "Impact coffee" }
							},
							{
								"link": { "url": "/", "label": "Table talk" }
							},
							{
								"link": { "url": "/", "label": "Push door" }
							}
						]
					}
				],
				company_description: "<p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. In blandit tincidunt id turpis est platea sed.</p>",
				heading: "Meet the Minds Shaping Our Industry",
				items: [
					{
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1542190891-2093d38760f2?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=774&q=80",
							"url": "https://images.unsplash.com/photo-1542190891-2093d38760f2?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=774&q=80",
							"size": null
						},
						"title": "Gustavo George",
						"subtitle": "Finance team lead",
						"description": {
							"html": "<p>Anim aute laboris laboris aliquip. Incididunt ipsum pariatur amet.</p>",
							"markdown": "Anim aute laboris laboris aliquip. Incididunt ipsum pariatur amet.\n\n"
						}
					},
					{
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1574842537689-5407308d37bb?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1856&q=80",
							"url": "https://images.unsplash.com/photo-1574842537689-5407308d37bb?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1856&q=80",
							"size": null
						},
						"title": "Essie Shay",
						"subtitle": "Finance agent",
						"description": {
							"html": "<p>Anim aute laboris laboris aliquip. Incididunt ipsum pariatur amet.</p>",
							"markdown": "Anim aute laboris laboris aliquip. Incididunt ipsum pariatur amet."
						}
					}
				]
			}
		});

	component_5 = new Component$6({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					},
					"title": ""
				},
				site_nav: [
					{ "link": { "url": "/", "label": "Home" } },
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: { "url": "/", "label": "Free Consultation" },
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Our values" }
							}
						]
					},
					{
						"label": "About",
						"link_list": [
							{
								"link": { "url": "/", "label": "Learn more" }
							},
							{
								"link": { "url": "/", "label": "Our team" }
							}
						]
					},
					{
						"label": "Legal",
						"link_list": [
							{ "link": { "url": "/", "label": "ut" } },
							{
								"link": { "url": "/", "label": "adipisicing" }
							}
						]
					}
				],
				company_description: {
					"html": "<p>Trusted financial services provider offering expert guidance, customized solutions, and peace of mind for all your financial needs.</p>",
					"markdown": "Trusted financial services provider offering expert guidance, customized solutions, and peace of mind for all your financial needs.\n\n"
				}
			}
		});

	component_6 = new Component$7({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-77' width='105' height='40' viewBox='0 0 105 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M48.136 35.2381H50.8704V24.9238H48.136V35.2381ZM48.136 23.3153H50.8704V20.8624H48.136V23.3153Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.6323 38.6159H55.3667V34.072H55.407C55.99 34.9566 56.935 35.5397 58.3826 35.5397C61.0366 35.5397 62.8461 33.4286 62.8461 30.091C62.8461 26.874 61.0969 24.6423 58.3625 24.6423C56.9551 24.6423 55.99 25.3058 55.3265 26.2105H55.2662V24.9238H52.6323V38.6159ZM57.7996 33.2677C56.171 33.2677 55.3064 32.0413 55.3064 30.1714C55.3064 28.3217 55.99 26.8539 57.699 26.8539C59.3879 26.8539 60.0715 28.2211 60.0715 30.1714C60.0715 32.1217 59.1869 33.2677 57.7996 33.2677Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.3007 35.5397C70.8742 35.5397 72.6435 34.2931 72.6435 32.2222C72.6435 29.8095 70.7335 29.327 69.0044 28.9651C67.5366 28.6635 66.1694 28.583 66.1694 27.6984C66.1694 26.9545 66.8731 26.5523 67.9388 26.5523C69.1049 26.5523 69.8086 26.9545 69.9292 28.0603H72.4023C72.2012 25.9894 70.6933 24.6423 67.979 24.6423C65.6266 24.6423 63.7768 25.7079 63.7768 27.9396C63.7768 30.1915 65.5864 30.6942 67.4361 31.0561C68.8435 31.3375 70.1504 31.4381 70.1504 32.4233C70.1504 33.1471 69.4668 33.6095 68.2604 33.6095C67.034 33.6095 66.1895 33.0868 66.0086 31.9005H63.4752C63.6361 34.0921 65.3049 35.5397 68.3007 35.5397Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M83.0252 35.2381V24.9238H80.2908V30.8751C80.2908 32.2423 79.5067 33.2074 78.2199 33.2074C77.0538 33.2074 76.5109 32.5439 76.5109 31.3375V24.9238H73.7966V31.8C73.7966 34.0518 75.0834 35.5196 77.3755 35.5196C78.8231 35.5196 79.6273 34.9767 80.3311 34.0317H80.3914V35.2381H83.0252Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M84.7939 35.2381H87.5284V29.2465C87.5284 27.8793 88.2723 26.9947 89.3781 26.9947C90.3834 26.9947 90.9665 27.5978 90.9665 28.764V35.2381H93.7009V29.2465C93.7009 27.8793 94.4046 26.9947 95.5506 26.9947C96.5559 26.9947 97.139 27.5978 97.139 28.764V35.2381H99.8734V28.3016C99.8734 26.0497 98.6469 24.6423 96.4755 24.6423C95.1686 24.6423 94.0829 25.3259 93.3792 26.4518H93.339C92.8363 25.3661 91.7908 24.6423 90.4839 24.6423C89.0564 24.6423 88.0511 25.3661 87.4881 26.3111H87.4278V24.9238H84.7939V35.2381Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.1762 17.572H50.9106V3.19629H48.1762V17.572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M57.5966 17.8736C60.7935 17.8736 62.985 15.5011 62.985 12.4249C62.985 9.3487 60.7935 6.97621 57.5966 6.97621C54.3998 6.97621 52.2082 9.3487 52.2082 12.4249C52.2082 15.5011 54.3998 17.8736 57.5966 17.8736ZM57.5966 15.7826C55.9077 15.7826 54.9829 14.4355 54.9829 12.4249C54.9829 10.4143 55.9077 9.04712 57.5966 9.04712C59.2654 9.04712 60.2104 10.4143 60.2104 12.4249C60.2104 14.4355 59.2654 15.7826 57.5966 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M68.8 21.0906C70.3281 21.0906 71.6551 20.7287 72.5196 19.9244C73.2836 19.2207 73.7461 18.2355 73.7461 16.7879V7.25769H71.1122V8.34341H71.072C70.4487 7.47885 69.5037 6.97621 68.2169 6.97621C65.6032 6.97621 63.7534 8.94659 63.7534 12.0228C63.7534 15.1392 66.0053 16.9487 68.2974 16.9487C69.6043 16.9487 70.3884 16.426 70.9916 15.7424H71.0519V16.8683C71.0519 18.2757 70.308 19.0196 68.7598 19.0196C67.4931 19.0196 66.9101 18.517 66.6889 17.8736H63.9746C64.2561 19.8842 65.9852 21.0906 68.8 21.0906ZM68.7598 14.7572C67.3524 14.7572 66.4275 13.7318 66.4275 11.9826C66.4275 10.2535 67.3524 9.16775 68.7397 9.16775C70.3884 9.16775 71.1926 10.4545 71.1926 11.9625C71.1926 13.4905 70.4889 14.7572 68.7598 14.7572Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M80.3925 17.8736C83.5893 17.8736 85.7809 15.5011 85.7809 12.4249C85.7809 9.3487 83.5893 6.97621 80.3925 6.97621C77.1957 6.97621 75.0041 9.3487 75.0041 12.4249C75.0041 15.5011 77.1957 17.8736 80.3925 17.8736ZM80.3925 15.7826C78.7036 15.7826 77.7787 14.4355 77.7787 12.4249C77.7787 10.4143 78.7036 9.04712 80.3925 9.04712C82.0613 9.04712 83.0063 10.4143 83.0063 12.4249C83.0063 14.4355 82.0613 15.7826 80.3925 15.7826Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M88.1779 13.6313H100V11.2789H88.1779V13.6313Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' d='M100.867 23.1717C100.867 22.709 101.242 22.3339 101.705 22.3339H103.38C103.843 22.3339 104.218 22.709 104.218 23.1717C104.218 23.6343 103.843 24.0094 103.38 24.0094H101.705C101.242 24.0094 100.867 23.6343 100.867 23.1717Z' fill='black'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M20.5216 0C31.5673 0 40.5216 8.9543 40.5216 20C40.5216 31.0457 31.5673 40 20.5216 40C9.47591 40 0.521606 31.0457 0.521606 20C0.521606 8.9543 9.47591 0 20.5216 0ZM19.7987 1.49659C17.5171 1.81769 15.3445 3.65108 13.658 6.7174C13.1688 7.60683 12.7274 8.58946 12.3427 9.65044C14.6359 9.07417 17.155 8.73442 19.7987 8.68187V1.49659ZM10.6524 10.1308C11.1307 8.62958 11.7159 7.2484 12.3912 6.02065C13.2272 4.50059 14.2194 3.18795 15.3373 2.17977C9.2584 3.94523 4.46683 8.73679 2.70138 14.8157C3.70955 13.6978 5.0222 12.7056 6.54226 11.8696C7.77001 11.1943 9.15118 10.6091 10.6524 10.1308ZM10.172 11.8211C9.59577 14.1143 9.25603 16.6334 9.20348 19.2771H2.01819C2.3393 16.9954 4.17269 14.8228 7.23901 13.1364C8.12844 12.6472 9.11107 12.2058 10.172 11.8211ZM10.6496 19.2771C10.7093 16.392 11.1246 13.6834 11.8118 11.2902C14.205 10.603 16.9137 10.1876 19.7987 10.1279V13.2508C18.7224 16.0062 16.5272 18.2012 13.7717 19.2771H10.6496ZM9.20348 20.7229H2.01819C2.3393 23.0046 4.17269 25.1771 7.23901 26.8636C8.12844 27.3528 9.11107 27.7942 10.172 28.1789C9.59577 25.8857 9.25603 23.3666 9.20348 20.7229ZM11.8118 28.7098C11.1246 26.3166 10.7093 23.608 10.6496 20.7229H13.7717C16.5272 21.7988 18.7225 23.9938 19.7987 26.7492V29.8721C16.9137 29.8124 14.205 29.397 11.8118 28.7098ZM10.6524 29.8692C9.15118 29.3909 7.77001 28.8057 6.54226 28.1304C5.0222 27.2944 3.70955 26.3022 2.70138 25.1843C4.46683 31.2632 9.2584 36.0548 15.3373 37.8202C14.2194 36.812 13.2272 35.4994 12.3912 33.9793C11.7159 32.7516 11.1307 31.3704 10.6524 29.8692ZM19.7987 38.5034C17.5171 38.1823 15.3445 36.3489 13.658 33.2826C13.1688 32.3932 12.7274 31.4105 12.3427 30.3496C14.6359 30.9258 17.155 31.2656 19.7987 31.3181V38.5034ZM25.7059 37.8202C26.8238 36.812 27.816 35.4994 28.6521 33.9793C29.3273 32.7516 29.9125 31.3704 30.3908 29.8692C31.892 29.3909 33.2732 28.8057 34.501 28.1304C36.021 27.2944 37.3337 26.3022 38.3418 25.1843C36.5764 31.2632 31.7848 36.0548 25.7059 37.8202ZM28.7005 30.3496C28.3158 31.4105 27.8744 32.3932 27.3852 33.2826C25.6988 36.3489 23.5262 38.1823 21.2445 38.5034V31.3181C23.8882 31.2656 26.4073 30.9258 28.7005 30.3496ZM30.8712 28.1789C31.9321 27.7942 32.9148 27.3528 33.8042 26.8636C36.8705 25.1771 38.7039 23.0046 39.025 20.7229H31.8397C31.7872 23.3666 31.4474 25.8857 30.8712 28.1789ZM30.3937 20.7229C30.334 23.608 29.9186 26.3166 29.2314 28.7098C26.8382 29.397 24.1296 29.8124 21.2445 29.8721V26.7515C22.3204 23.9951 24.5161 21.7991 27.2724 20.7229H30.3937ZM31.8397 19.2771H39.025C38.7039 16.9954 36.8705 14.8228 33.8042 13.1364C32.9148 12.6472 31.9321 12.2058 30.8712 11.8211C31.4474 14.1143 31.7872 16.6334 31.8397 19.2771ZM29.2314 11.2902C29.9186 13.6834 30.334 16.392 30.3937 19.2771H27.2724C24.5161 18.2009 22.3204 16.0049 21.2445 13.2485V10.1279C24.1296 10.1876 26.8382 10.603 29.2314 11.2902ZM30.3908 10.1308C31.892 10.6091 33.2732 11.1943 34.501 11.8696C36.021 12.7056 37.3337 13.6978 38.3418 14.8157C36.5764 8.73679 31.7848 3.94523 25.7059 2.17977C26.8238 3.18795 27.816 4.50059 28.6521 6.02065C29.3273 7.2484 29.9125 8.62958 30.3908 10.1308ZM21.2445 1.49659C23.5262 1.81769 25.6988 3.65108 27.3852 6.7174C27.8744 7.60684 28.3158 8.58946 28.7005 9.65044C26.4073 9.07417 23.8882 8.73442 21.2445 8.68187V1.49659Z' fill='black'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{ "link": { "url": "/", "label": "Home" } },
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": { "url": "/services", "label": "Services" }
					}
				],
				primary_cta: { "url": "/", "label": "Free Consultation" },
				footer_links: [
					{
						"label": "Company",
						"link_list": [
							{
								"link": { "url": "/", "label": "Global location" }
							},
							{
								"link": { "url": "/", "label": "Missions" }
							},
							{
								"link": { "url": "/", "label": "Careers" }
							},
							{
								"link": { "url": "/", "label": "Investors" }
							},
							{
								"link": { "url": "/", "label": "News rooms" }
							}
						]
					},
					{
						"label": "Impact",
						"link_list": [
							{
								"link": { "url": "/", "label": "Creator awards" }
							},
							{
								"link": { "url": "/", "label": "Creative ideas" }
							},
							{
								"link": {
									"url": "/",
									"label": "Refuge initiatives"
								}
							},
							{
								"link": { "url": "/", "label": "Residents" }
							}
						]
					},
					{
						"label": "Partnership",
						"link_list": [
							{
								"link": { "url": "/", "label": "Brokers" }
							},
							{
								"link": { "url": "/", "label": "Impact coffee" }
							},
							{
								"link": { "url": "/", "label": "Table talk" }
							},
							{
								"link": { "url": "/", "label": "Push door" }
							}
						]
					}
				],
				company_description: "<p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. In blandit tincidunt id turpis est platea sed.</p>"
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
		}
	};
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$7, safe_not_equal, {});
	}
}

export default Component$8;
