import asyncio
import uuid
from collections import OrderedDict, deque
from queue import Queue


def safe_rm(queue, id, repl):
    """Safely remove a REPL instance from the queue."""
    try:
        queue.remove((id, repl))
        return True
    except ValueError:
        return False


class LRUReplCache:
    def __init__(self, max_size=500):
        self.cache = {}  # The cache that will store REPL pools
        self.global_repl_pool = (
            OrderedDict()
        )  # A list to track all REPLs globally for LRU eviction
        self.max_size = max_size  # Max number of REPLs globally
        self.lock = asyncio.Lock()  # Lock to ensure exclusive access to each REPL
        self.close_queue = Queue()  # Queue to store REPLs that need to be closed
        self.create_queue = []  # Queue to store REPLs that need to be created
        self.stats = {
            "cache_hits": 0,
            "cache_misses": 0,
        }

    async def get(self, key):
        """Get a REPL instance for the given header key."""
        async with self.lock:  # Ensure thread-safety
            if key in self.cache and self.cache[key]:
                id, repl = self.cache[key].pop()
                # Move this REPL to the global LRU list to mark it as recently used
                assert id in self.global_repl_pool
                self.global_repl_pool.move_to_end(id)
                self.stats["cache_hits"] += 1
                return id, repl
            self.stats["cache_misses"] += 1
            return None, None

    async def put(self, key, repl):
        """Put a new REPL instance into the cache for a specific header."""
        async with self.lock:
            if key not in self.cache:
                self.cache[key] = deque()

            # Add the new REPL to the list for that header
            id = uuid.uuid4()
            self.cache[key].append((id, repl))
            # Also add it to the global LRU list
            self.global_repl_pool[id] = (key, repl)
            self._evict_if_needed()

    def _evict_if_needed(self):
        """Evict the least recently used REPLs globally if the cache size exceeds the max size."""
        if len(self.global_repl_pool) > self.max_size:
            # Pop the oldest item from the global LRU list (least recently used)
            while len(self.global_repl_pool) > self.max_size:
                id, (header_key, repl) = self.global_repl_pool.popitem(
                    last=False
                )  # Pop the oldest item

                # Evict the REPL instance from the cache as well
                if self.cache[header_key] and safe_rm(self.cache[header_key], id, repl):
                    print(
                        f"Succesfully evicted header {str([header_key])[:30]} with id {str(id)}"
                    )
                    self.close_queue.put((id, repl))
                else:
                    print(
                        f"Failed to evict header {str([header_key])[:30]} with id {str(id)}, putting it back"
                    )
                    self.global_repl_pool[id] = (header_key, repl)

    async def destroy(self, key, id, repl):
        """Close a REPL instance and remove it from the cache."""
        print(f"Destroying header {str([key])[:30]} with id {str(id)}")
        async with self.lock:
            # Remove the REPL from the cache
            if key in self.cache:
                safe_rm(self.cache[key], id, repl)

            # Remove the REPL from the global LRU list
            if id in self.global_repl_pool:
                del self.global_repl_pool[id]
            # Close the REPL instance
            self.close_queue.put((id, repl))

    async def release(self, key, id, repl):
        """Release a REPL back to the cache, marking it as recently used."""
        async with self.lock:
            # Remove and then re-add the REPL to mark it as recently used
            if key in self.cache:
                self.cache[key].append((id, repl))
                self.global_repl_pool.move_to_end(id)

    def create(self, header):
        """Create a new REPL instance for a specific header."""
        self.create_queue.append(header)

    def size(self):
        """Get the current size of the cache."""
        return len(self.global_repl_pool)

    async def clean_cache_entry(self):
        """Clean cache entry with empty queue."""
        deleted_headers = []
        async with self.lock:
            for header in list(self.cache.keys()):
                if not self.cache[header]:
                    del self.cache[header]
                    deleted_headers.append(header)
        print("[Clean cache entry] Num deleted headers: ", len(deleted_headers))

    async def print_status(self, update_interval=5):
        """Print the current status of the cache."""
        # Print the header
        print("=" * 65)
        print(f"{'Idx':<5} | {'Header':<45} | {'Pool Size':<10}")
        print("-" * 65)

        idx = 1
        idle_count = 0

        async with self.lock:
            # Print the cache status
            proof_headers = list(self.cache.keys())
            qsizes = [len(self.cache[header]) for header in proof_headers]
        proof_headers_and_qsizes = sorted(
            zip(proof_headers, qsizes), key=lambda x: x[1], reverse=True
        )

        for header, qsize in proof_headers_and_qsizes:
            proof_header = str([header])[:43]
            if idx < 30:
                print(f"{idx:<5} | {proof_header:<45} | {qsize:<10}")
            elif idx == 30:
                print(f"{'...':<5} | {'...':<45} | {'...':<10}")
            idx += 1
            idle_count += qsize

        print("-" * 65)
        # print top 10 global LRU pool
        print("Top 10 global LRU repl:")
        print("-" * 65)
        print(f"{'Idx':<5} | {'Header':<45} | {'ID':<10}")
        print("-" * 65)

        # reverse iteration on global_repl_pool
        async with self.lock:
            for idx, (id, (header, _)) in enumerate(
                reversed(list(self.global_repl_pool.items()))
            ):
                header = str([header])[:43]
                if idx < 10:
                    print(f"{idx + 1:<5} | {header:<45} | {str(id)[:8]:<10}")
                elif idx == 10:
                    print(f"{'...':<5} | {'...':<45} | {'...':<10}")
                    break

        print("-" * 65)
        print(f"{'':<5} | {'Total':<45} | {len(self.global_repl_pool):<10}")
        print(f"{'':<5} | {'Idle':<45} | {idle_count:<10}")
        print(f"{'':<5} | {'Create Queue':<45} | {len(self.create_queue):<10}")
        print(f"{'':<5} | {'Close Queue':<45} | {self.close_queue.qsize():<10}")
        print(f"{'':<5} | {'Cache Hits':<45} | {self.stats['cache_hits']:<10}")
        print(f"{'':<5} | {'Cache Misses':<45} | {self.stats['cache_misses']:<10}")
        print(
            f"{'':<5} | {'Cache ratio':<45} | {self.stats['cache_hits'] / (self.stats['cache_hits'] + self.stats['cache_misses'] + 1):<10.2f}"
        )
        print(
            f"{'':<5} | {'its':<45} | {(self.stats['cache_hits'] + self.stats['cache_misses']) / update_interval:<10}"
        )
        print("=" * 65)

        self.stats["cache_hits"] = 0
        self.stats["cache_misses"] = 0
