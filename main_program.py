"""A complete desktop airline booking system with 10 Data Structure and Algorithmic techniques:
1. Array / List (Flight catalog & tabular UI rendering)
2. Stack (LIFO for booking undo operations)
3. Queue & Priority Queue / Max Heap (VIP / Business / Economy priority request handling)
   + FIFO Waitlist Queues (deque) for seat conflicts and full flights
4. Singly Linked List (Node-based storage for confirmed bookings)
5. Binary Search Tree / BST (O(log n) flight lookup by flight number)
6. Weighted Graph & Dijkstra's Algorithm (Adjacency List with BFS and Dijkstra shortest path)
7. QuickSort Algorithm (Manual O(n log n) sorting on table column headers)
8. Hash Table with Chaining (O(1) passenger booking indexing)
9. Interactive Seat Map (Visual seating assignment grid)
10. E-Ticket Generator (File generation & export)
"""

from collections import deque
from dataclasses import dataclass, field
from itertools import count
import json
import heapq
from pathlib import Path
import tkinter as tk
from tkinter import messagebox, ttk


# ============================================================================
# 1. DATA MODELS & PRIMITIVE STRUCTURES
# ============================================================================

@dataclass
class Flight:
    """A flight record with pricing and capacity management."""
    flight_number: str
    origin: str
    destination: str
    departure_time: str
    capacity: int
    price: float
    duration_mins: int
    booked_seats: int = 0
    occupied_seats_set: set[str] = field(default_factory=set)

    def __post_init__(self) -> None:
        if not self.flight_number.strip():
            raise ValueError("Flight number cannot be empty.")
        if self.capacity <= 0:
            raise ValueError("Flight capacity must be greater than zero.")
        if not 0 <= self.booked_seats <= self.capacity:
            raise ValueError("Booked seats must be within capacity.")

    @property
    def available_seats(self) -> int:
        return self.capacity - self.booked_seats

    def reserve_seat(self, specific_seat: str | None = None) -> str:
        if self.available_seats <= 0:
            raise ValueError(f"Flight {self.flight_number} is fully booked.")

        if specific_seat:
            if specific_seat in self.occupied_seats_set:
                raise ValueError(f"Seat {specific_seat} is already occupied on flight {self.flight_number}.")
            seat_code = specific_seat
        else:
            seat_code = self._get_next_available_seat_code()

        self.booked_seats += 1
        self.occupied_seats_set.add(seat_code)
        return seat_code

    def release_seat(self, seat_code: str) -> None:
        if seat_code in self.occupied_seats_set:
            self.occupied_seats_set.remove(seat_code)
            self.booked_seats = max(0, self.booked_seats - 1)

    def _get_next_available_seat_code(self) -> str:
        seat_letters = ["A", "B", "C", "D"]
        max_rows = (self.capacity + 3) // 4
        for r in range(1, max_rows + 1):
            for l in seat_letters:
                code = f"{r}{l}"
                if code not in self.occupied_seats_set:
                    return code
        return f"S-{self.booked_seats + 1:03d}"


@dataclass(frozen=True)
class Passenger:
    """Passenger entity with ticket class tier."""
    name: str
    ticket_class: str = "Economy"  # VIP, Business, Economy

    def __post_init__(self) -> None:
        if not self.name.strip():
            raise ValueError("Passenger name cannot be empty.")


@dataclass(order=True)
class BookingRequest:
    """Request element in Priority Queue (Heap). Sorted by priority_score (higher first)."""
    priority_score: int
    request_id: int
    passenger: Passenger = field(compare=False)
    flight_number: str = field(compare=False)
    requested_seat: str | None = field(default=None, compare=False)


@dataclass(frozen=True)
class Booking:
    """Confirmed booking record."""
    booking_id: int
    passenger: Passenger
    flight_number: str
    seat_number: str
    fare: float


# ============================================================================
# 2. STACK DATA STRUCTURE (Module 2: LIFO)
# ============================================================================

class Stack:
    """Last In, First Out (LIFO) Stack for Undo Operations."""
    def __init__(self) -> None:
        self._items: list[Booking] = []

    def push(self, item: Booking) -> None:
        self._items.append(item)

    def pop(self) -> Booking | None:
        if self.is_empty():
            return None
        return self._items.pop()

    def remove(self, item: Booking) -> bool:
        """Remove a specific booking from anywhere in the stack (used when cancelling)."""
        if item in self._items:
            self._items.remove(item)
            return True
        return False

    def is_empty(self) -> bool:
        return len(self._items) == 0


# ============================================================================
# 3. LINKED LIST DATA STRUCTURE (Module 3: Dynamic Singly Linked List)
# ============================================================================

class LinkedListNode:
    """Node for Singly Linked List containing data and pointer to next node."""
    def __init__(self, booking: Booking) -> None:
        self.data: Booking = booking
        self.next: LinkedListNode | None = None


class SinglyLinkedList:
    """Singly Linked List for managing confirmed bookings dynamically."""
    def __init__(self) -> None:
        self.head: LinkedListNode | None = None

    def append(self, booking: Booking) -> None:
        new_node = LinkedListNode(booking)
        if not self.head:
            self.head = new_node
            return
        curr = self.head
        while curr.next:
            curr = curr.next
        curr.next = new_node

    def remove(self, booking: Booking) -> bool:
        if not self.head:
            return False
        if self.head.data == booking:
            self.head = self.head.next
            return True
        curr = self.head
        while curr.next:
            if curr.next.data == booking:
                curr.next = curr.next.next
                return True
            curr = curr.next
        return False

    def to_list(self) -> list[Booking]:
        result = []
        curr = self.head
        while curr:
            result.append(curr.data)
            curr = curr.next
        return result


# ============================================================================
# 4. BINARY SEARCH TREE (Module 4 & 6: BST)
# ============================================================================

class BSTNode:
    """Binary Search Tree Node for Flight indexing."""
    def __init__(self, flight: Flight) -> None:
        self.flight: Flight = flight
        self.left: BSTNode | None = None
        self.right: BSTNode | None = None


class FlightBST:
    """Binary Search Tree for O(log n) Flight Searching by Flight Number."""
    def __init__(self) -> None:
        self.root: BSTNode | None = None

    def insert(self, flight: Flight) -> None:
        self.root = self._insert_recursive(self.root, flight)

    def _insert_recursive(self, node: BSTNode | None, flight: Flight) -> BSTNode:
        if node is None:
            return BSTNode(flight)
        if flight.flight_number < node.flight.flight_number:
            node.left = self._insert_recursive(node.left, flight)
        elif flight.flight_number > node.flight.flight_number:
            node.right = self._insert_recursive(node.right, flight)
        return node

    def search(self, flight_number: str) -> Flight | None:
        return self._search_recursive(self.root, flight_number.strip().upper())

    def _search_recursive(self, node: BSTNode | None, flight_number: str) -> Flight | None:
        if node is None or node.flight.flight_number == flight_number:
            return node.flight if node else None
        if flight_number < node.flight.flight_number:
            return self._search_recursive(node.left, flight_number)
        return self._search_recursive(node.right, flight_number)

    def get_all_flights(self) -> list[Flight]:
        flights = []
        self._inorder(self.root, flights)
        return flights

    def _inorder(self, node: BSTNode | None, flights: list[Flight]) -> None:
        if node:
            self._inorder(node.left, flights)
            flights.append(node.flight)
            self._inorder(node.right, flights)


# ============================================================================
# 5. WEIGHTED GRAPH & DIJKSTRA'S ALGORITHM (Module 5)
# ============================================================================

class FlightGraph:
    """Graph representing Airport Routes (Vertices = Cities, Edges = Flights with Prices)."""
    def __init__(self) -> None:
        self.adj_list: dict[str, list[tuple[str, str, float, int]]] = {}

    def add_route(self, origin: str, destination: str, flight_number: str, price: float, duration: int) -> None:
        if origin not in self.adj_list:
            self.adj_list[origin] = []
        if destination not in self.adj_list:
            self.adj_list[destination] = []
        self.adj_list[origin].append((destination, flight_number, price, duration))

    def find_route_bfs(self, start: str, end: str) -> list[str] | None:
        """BFS for unweighted shortest path (fewest flight legs)."""
        start, end = start.strip().title(), end.strip().title()
        if start not in self.adj_list or end not in self.adj_list:
            return None

        visited = set([start])
        queue: deque[list[str]] = deque([[start]])

        while queue:
            path = queue.popleft()
            node = path[-1]

            if node == end:
                return path

            for neighbor, _, _, _ in self.adj_list.get(node, []):
                if neighbor not in visited:
                    visited.add(neighbor)
                    new_path = list(path)
                    new_path.append(neighbor)
                    queue.append(new_path)

        return None

    def find_cheapest_route_dijkstra(self, start: str, end: str) -> tuple[list[str], float, list[str]] | None:
        """Dijkstra's Algorithm to find the lowest total cost route path."""
        start, end = start.strip().title(), end.strip().title()
        if start not in self.adj_list or end not in self.adj_list:
            return None

        pq = [(0.0, start, [start], [])]
        distances = {city: float('inf') for city in self.adj_list}
        distances[start] = 0.0

        while pq:
            cost, current, path, flight_nos = heapq.heappop(pq)

            if current == end:
                return path, cost, flight_nos

            if cost > distances[current]:
                continue

            for neighbor, flight_no, price, _ in self.adj_list.get(current, []):
                new_cost = cost + price
                if new_cost < distances.get(neighbor, float('inf')):
                    distances[neighbor] = new_cost
                    heapq.heappush(pq, (new_cost, neighbor, path + [neighbor], flight_nos + [flight_no]))

        return None


# ============================================================================
# 6. PRIORITY QUEUE (MAX HEAP FOR PASSENGERS)
# ============================================================================

class PriorityBookingQueue:
    """Priority Queue / Max Heap for VIP, Business, and Economy passengers."""
    TIER_SCORES = {"VIP": 100, "Business": 50, "Economy": 10}

    def __init__(self) -> None:
        self._heap: list[BookingRequest] = []
        self._counter = count(1)

    def enqueue(self, passenger: Passenger, flight_number: str, requested_seat: str | None = None) -> BookingRequest:
        tier_score = self.TIER_SCORES.get(passenger.ticket_class, 10)
        req_id = next(self._counter)
        req = BookingRequest(
            priority_score=-tier_score,
            request_id=req_id,
            passenger=passenger,
            flight_number=flight_number,
            requested_seat=requested_seat
        )
        heapq.heappush(self._heap, req)
        return req

    def dequeue(self) -> BookingRequest | None:
        if not self._heap:
            return None
        return heapq.heappop(self._heap)

    def to_sorted_list(self) -> list[BookingRequest]:
        return sorted(self._heap)

    def is_empty(self) -> bool:
        return len(self._heap) == 0


# ============================================================================
# 6b. WAITLIST (FIFO QUEUES)
# ============================================================================

class WaitlistManager:
    """FIFO queues (deque) keyed by (flight_number, seat). Seat 'ANY' = flight is full."""
    def __init__(self) -> None:
        self._lists: dict[tuple[str, str], deque[BookingRequest]] = {}

    def add(self, req: BookingRequest, seat: str | None = None) -> int:
        """Add a request to the waitlist. Returns the position in line (1-based)."""
        key = (req.flight_number, seat or "ANY")
        q = self._lists.setdefault(key, deque())
        q.append(req)
        return len(q)

    def pop_for_seat(self, flight_number: str, seat: str) -> BookingRequest | None:
        """Specific-seat waiters get priority, then the general flight waitlist."""
        for key in ((flight_number, seat), (flight_number, "ANY")):
            q = self._lists.get(key)
            if q:
                return q.popleft()
        return None

    def entries(self) -> list[tuple[str, str, int, BookingRequest]]:
        rows = []
        for (flight, seat), q in self._lists.items():
            for pos, req in enumerate(q, start=1):
                rows.append((flight, seat, pos, req))
        return rows

    def clear(self) -> None:
        self._lists.clear()

    def to_dicts(self) -> list[dict]:
        """Serialize every waitlisted request (in FIFO order per queue) for JSON."""
        return [
            {
                "flight_number": flight,
                "waitlist_seat": seat,  # specific seat code, or "ANY" for a full flight
                "request_id": req.request_id,
                "passenger_name": req.passenger.name,
                "ticket_class": req.passenger.ticket_class,
                "requested_seat": req.requested_seat,
            }
            for flight, seat, _pos, req in self.entries()
        ]

    def restore(self, items: list[dict]) -> None:
        """Rebuild the queues from saved JSON, preserving the original FIFO order."""
        self.clear()
        for item in items:
            passenger = Passenger(item["passenger_name"], item.get("ticket_class", "Economy"))
            score = PriorityBookingQueue.TIER_SCORES.get(passenger.ticket_class, 10)
            req = BookingRequest(
                priority_score=-score,
                request_id=item.get("request_id", 0),
                passenger=passenger,
                flight_number=item["flight_number"],
                requested_seat=item.get("requested_seat"),
            )
            seat = item.get("waitlist_seat", "ANY")
            self.add(req, None if seat == "ANY" else seat)


# ============================================================================
# 7. MANUAL QUICKSORT ALGORITHM
# ============================================================================

def quicksort_flights(flights: list[Flight], key_func, reverse: bool = False) -> list[Flight]:
    """Manual QuickSort O(n log n) implementation for catalog sorting."""
    if len(flights) <= 1:
        return flights
    pivot = flights[len(flights) // 2]
    pivot_val = key_func(pivot)

    left = [x for x in flights if key_func(x) < pivot_val]
    middle = [x for x in flights if key_func(x) == pivot_val]
    right = [x for x in flights if key_func(x) > pivot_val]

    if reverse:
        return quicksort_flights(right, key_func, reverse) + middle + quicksort_flights(left, key_func, reverse)
    return quicksort_flights(left, key_func, reverse) + middle + quicksort_flights(right, key_func, reverse)


# ============================================================================
# 8. HASH TABLE WITH CHAINING (O(1) Passenger Indexing)
# ============================================================================

class HashTable:
    """Hash Map with Chaining for O(1) average lookup of passenger bookings."""
    def __init__(self, capacity: int = 64) -> None:
        self.capacity = capacity
        self.buckets: list[list[tuple[str, Booking]]] = [[] for _ in range(capacity)]

    def _hash(self, key: str) -> int:
        return hash(key.strip().lower()) % self.capacity

    def put(self, key: str, booking: Booking) -> None:
        bucket = self.buckets[self._hash(key)]
        bucket.append((key.strip().lower(), booking))

    def get(self, key: str) -> list[Booking]:
        bucket = self.buckets[self._hash(key)]
        search_key = key.strip().lower()
        return [booking for k, booking in bucket if k == search_key]

    def remove(self, booking: Booking) -> None:
        bucket = self.buckets[self._hash(booking.passenger.name)]
        self.buckets[self._hash(booking.passenger.name)] = [
            (k, b) for k, b in bucket if b.booking_id != booking.booking_id
        ]


# ============================================================================
# 9. CENTRAL SYSTEM FACADE MANAGER
# ============================================================================

class AirlineBookingSystem:
    """Central manager unifying all Data Structure and Algorithmic techniques."""

    def __init__(self, flights: list[Flight]) -> None:
        if not flights:
            raise ValueError("At least one flight must be provided.")

        self._raw_flights = list(flights)
        self._flight_bst = FlightBST()
        self._flight_graph = FlightGraph()

        for flight in flights:
            self._flight_bst.insert(flight)
            self._flight_graph.add_route(
                flight.origin, flight.destination, flight.flight_number, flight.price, flight.duration_mins
            )

        self._priority_queue = PriorityBookingQueue()
        self._waitlist = WaitlistManager()
        self._bookings_linked_list = SinglyLinkedList()
        self._booking_stack = Stack()
        self._hash_table = HashTable()
        self._booking_ids = count(1)
        self.load_from_json()

    @property
    def flights(self) -> list[Flight]:
        return self._flight_bst.get_all_flights()

    @property
    def pending_requests(self) -> list[BookingRequest]:
        return self._priority_queue.to_sorted_list()

    @property
    def bookings(self) -> list[Booking]:
        return self._bookings_linked_list.to_list()

    @property
    def waitlist_entries(self) -> list[tuple[str, str, int, BookingRequest]]:
        return self._waitlist.entries()

    def search_flight_bst(self, flight_number: str) -> Flight | None:
        return self._flight_bst.search(flight_number)

    def find_city_route_bfs(self, origin: str, destination: str) -> list[str] | None:
        return self._flight_graph.find_route_bfs(origin, destination)

    def find_cheapest_route_dijkstra(self, origin: str, destination: str):
        return self._flight_graph.find_cheapest_route_dijkstra(origin, destination)

    def sort_flights(self, key_name: str, reverse: bool = False) -> list[Flight]:
        key_funcs = {
            "flight": lambda f: f.flight_number,
            "price": lambda f: f.price,
            "duration": lambda f: f.duration_mins,
            "seats": lambda f: f.available_seats,
        }
        return quicksort_flights(self.flights, key_funcs.get(key_name, lambda f: f.flight_number), reverse)

    def search_passenger_hash(self, passenger_name: str) -> list[Booking]:
        return self._hash_table.get(passenger_name)

    def enqueue_booking(self, passenger_name: str, flight_number: str, ticket_class: str = "Economy", specific_seat: str | None = None) -> None:
        flight = self.search_flight_bst(flight_number)
        if not flight:
            raise ValueError(f"Unknown flight number: {flight_number}")
        passenger = Passenger(passenger_name.strip(), ticket_class)
        self._priority_queue.enqueue(passenger, flight_number, specific_seat)

    def _confirm_booking(self, req: BookingRequest, flight: Flight, seat_code: str) -> Booking:
        """Shared code path: create a Booking and register it in every structure."""
        booking = Booking(
            booking_id=next(self._booking_ids),
            passenger=req.passenger,
            flight_number=flight.flight_number,
            seat_number=seat_code,
            fare=flight.price,
        )
        self._bookings_linked_list.append(booking)
        self._booking_stack.push(booking)
        self._hash_table.put(req.passenger.name, booking)
        return booking

    def process_booking_queue(self) -> list[str]:
        results = []
        while not self._priority_queue.is_empty():
            req = self._priority_queue.dequeue()
            flight = self.search_flight_bst(req.flight_number)
            if not flight:
                results.append(f"Unknown flight {req.flight_number} for {req.passenger.name}.")
                continue

            seat_taken = bool(req.requested_seat) and req.requested_seat in flight.occupied_seats_set
            if flight.available_seats == 0 or seat_taken:
                # Seat conflict or full flight -> FIFO waitlist instead of failing
                position = self._waitlist.add(req, req.requested_seat if seat_taken else None)
                reason = f"seat {req.requested_seat} taken" if seat_taken else "flight full"
                results.append(
                    f"[WAITLIST] {req.passenger.name} on {req.flight_number} "
                    f"({reason}) - position #{position}"
                )
                continue

            seat_code = flight.reserve_seat(req.requested_seat)
            booking = self._confirm_booking(req, flight, seat_code)
            results.append(
                f"[{req.passenger.ticket_class}] Confirmed #{booking.booking_id} for "
                f"{booking.passenger.name} ({booking.flight_number}, Seat {seat_code}, ₱{booking.fare:,.2f})"
            )

        self.save_to_json()
        return results

    def _release_booking(self, booking: Booking) -> list[str]:
        """Remove a booking from every structure, free the seat, and promote the waitlist."""
        self._bookings_linked_list.remove(booking)
        self._booking_stack.remove(booking)
        self._hash_table.remove(booking)

        notes: list[str] = []
        flight = self.search_flight_bst(booking.flight_number)
        if flight:
            flight.release_seat(booking.seat_number)
            next_req = self._waitlist.pop_for_seat(flight.flight_number, booking.seat_number)
            if next_req:
                seat = flight.reserve_seat(booking.seat_number)
                new_booking = self._confirm_booking(next_req, flight, seat)
                notes.append(
                    f"Waitlist promoted: {new_booking.passenger.name} -> "
                    f"#{new_booking.booking_id} (Seat {new_booking.seat_number})"
                )

        # Invalidate the boarding pass file of the cancelled booking
        ticket = Path(f"e_ticket_booking_{booking.booking_id}.txt")
        if ticket.exists():
            ticket.unlink()

        self.save_to_json()
        return notes

    def undo_last_booking(self) -> tuple[Booking, list[str]] | None:
        booking = self._booking_stack.pop()
        if booking is None:
            return None
        return booking, self._release_booking(booking)

    def cancel_booking(self, booking_id: int) -> tuple[Booking, list[str]] | None:
        booking = next((b for b in self.bookings if b.booking_id == booking_id), None)
        if booking is None:
            return None
        return booking, self._release_booking(booking)

    def generate_e_ticket(self, booking: Booking) -> str:
        flight = self.search_flight_bst(booking.flight_number)
        origin = flight.origin if flight else "N/A"
        destination = flight.destination if flight else "N/A"

        ticket_str = f"""==================================================
           AIRLINE ELECTRONIC BOARDING PASS       
==================================================
Booking Ref ID : #{booking.booking_id}
Passenger Name : {booking.passenger.name}
Ticket Class   : {booking.passenger.ticket_class}
--------------------------------------------------
Flight Number  : {booking.flight_number}
Route          : {origin} -> {destination}
Assigned Seat  : {booking.seat_number}
Total Fare     : ₱{booking.fare:,.2f}
==================================================
        Thank you for flying with us!
"""
        filename = f"e_ticket_booking_{booking.booking_id}.txt"
        with open(filename, "w", encoding="utf-8") as f:
            f.write(ticket_str)
        return filename

    def add_new_flight(self, flight_number: str, origin: str, destination: str, departure: str, capacity: int, price: float, duration: int) -> None:
        new_flight = Flight(flight_number, origin, destination, departure, capacity, price, duration)
        self._flight_bst.insert(new_flight)
        self._flight_graph.add_route(origin, destination, flight_number, price, duration)

    def reset_system_data(self, filepath: str = "bookings.json") -> None:
        path = Path(filepath)
        if path.exists():
            path.unlink()
        self._bookings_linked_list = SinglyLinkedList()
        self._booking_stack = Stack()
        self._hash_table = HashTable()
        self._priority_queue = PriorityBookingQueue()
        self._waitlist.clear()
        self._booking_ids = count(1)
        for f in self.flights:
            f.booked_seats = 0
            f.occupied_seats_set.clear()

    def save_to_json(self, filepath: str = "bookings.json") -> None:
        data = {
            "bookings": [
                {
                    "booking_id": b.booking_id,
                    "passenger_name": b.passenger.name,
                    "ticket_class": b.passenger.ticket_class,
                    "flight_number": b.flight_number,
                    "seat_number": b.seat_number,
                    "fare": b.fare
                }
                for b in self.bookings
            ],
            "waitlist": self._waitlist.to_dicts(),
        }
        with open(filepath, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=4)

    def load_from_json(self, filepath: str = "bookings.json") -> None:
        path = Path(filepath)
        if not path.exists():
            return

        with open(filepath, "r", encoding="utf-8") as f:
            raw = json.load(f)

        # Backward compatible: the old format was a plain list of bookings.
        if isinstance(raw, list):
            booking_items, waitlist_items = raw, []
        else:
            booking_items = raw.get("bookings", [])
            waitlist_items = raw.get("waitlist", [])

        max_id = 0
        for item in booking_items:
            flight = self.search_flight_bst(item["flight_number"])
            if flight and flight.available_seats > 0:
                seat_num = item.get("seat_number", "1A")
                flight.reserve_seat(seat_num)
                booking = Booking(
                    booking_id=item["booking_id"],
                    passenger=Passenger(item["passenger_name"], item.get("ticket_class", "Economy")),
                    flight_number=item["flight_number"],
                    seat_number=seat_num,
                    fare=item.get("fare", flight.price)
                )
                self._bookings_linked_list.append(booking)
                self._booking_stack.push(booking)
                self._hash_table.put(item["passenger_name"], booking)
                if item["booking_id"] > max_id:
                    max_id = item["booking_id"]

        self._booking_ids = count(max_id + 1)

        # Only restore waitlist entries for flights that still exist
        valid_waitlist = [w for w in waitlist_items if self.search_flight_bst(w["flight_number"])]
        self._waitlist.restore(valid_waitlist)


# ============================================================================
# 10. TKINTER USER INTERFACE & DIALOGS
# ============================================================================

class SeatPickerWindow(tk.Toplevel):
    """Interactive seat map picker modal dialog."""
    def __init__(self, parent, flight: Flight, on_seat_selected):
        super().__init__(parent)
        self.title(f"Seat Map - {flight.flight_number}")
        self.geometry("380x480")
        self.resizable(False, False)
        self.flight = flight
        self.on_seat_selected = on_seat_selected
        self.selected_seat = None

        ttk.Label(self, text=f"Select Seat for {flight.flight_number}", font=("Segoe UI", 12, "bold")).pack(pady=10)
        ttk.Label(self, text=f"Green = Available | Red = Occupied", font=("Segoe UI", 9)).pack(pady=(0, 10))

        frame = ttk.Frame(self, padding=10)
        frame.pack(fill="both", expand=True)

        rows = (flight.capacity + 3) // 4
        seat_letters = ["A", "B", "C", "D"]

        for r in range(1, rows + 1):
            ttk.Label(frame, text=f"Row {r}", font=("Segoe UI", 8)).grid(row=r, column=0, padx=5, pady=2)
            for c_idx, letter in enumerate(seat_letters, start=1):
                col = c_idx if c_idx <= 2 else c_idx + 1 # Leave aisle space
                code = f"{r}{letter}"
                is_occupied = code in flight.occupied_seats_set

                btn_color = "#e53e3e" if is_occupied else "#38a169"
                btn_state = "disabled" if is_occupied else "normal"

                btn = tk.Button(
                    frame,
                    text=code,
                    width=4,
                    bg=btn_color,
                    fg="white",
                    state=btn_state,
                    command=lambda s=code: self._select(s)
                )
                btn.grid(row=r, column=col, padx=2, pady=2)

    def _select(self, seat_code: str):
        self.selected_seat = seat_code
        self.on_seat_selected(seat_code)
        self.destroy()


class AirlineBookingApp:
    """Advanced Tkinter Desktop UI for Airline Desk Management."""

    def __init__(self, root: tk.Tk, system: AirlineBookingSystem) -> None:
        self.root = root
        self.system = system
        self.is_admin_mode = tk.BooleanVar(value=False)
        self.selected_seat_code = tk.StringVar(value="")
        self.status_text = tk.StringVar(value="System active. All 10 Data Structure techniques loaded.")
        self.sort_state = {"col": "flight", "reverse": False}

        self.root.title("Enterprise Airline Booking Desk (10 DS & Algorithms Edition)")
        self.root.geometry("1200x880")
        self.root.minsize(1000, 700)
        self.root.configure(background="#f3f6fb")

        self._configure_styles()
        self._build_interface()
        self._refresh_tables()

    def _configure_styles(self) -> None:
        style = ttk.Style(self.root)
        style.theme_use("clam")
        style.configure("App.TFrame", background="#f3f6fb")
        style.configure("Card.TFrame", background="#ffffff")
        style.configure("Title.TLabel", background="#f3f6fb", foreground="#102a43", font=("Segoe UI", 20, "bold"))
        style.configure("Subtitle.TLabel", background="#f3f6fb", foreground="#52667a", font=("Segoe UI", 9))
        style.configure("Section.TLabel", background="#ffffff", foreground="#102a43", font=("Segoe UI", 11, "bold"))
        style.configure("CardText.TLabel", background="#ffffff", foreground="#52667a", font=("Segoe UI", 9))
        style.configure("Treeview", rowheight=26, background="#ffffff", fieldbackground="#ffffff", foreground="#243b53", font=("Segoe UI", 9))
        style.configure("Treeview.Heading", background="#eaf0f7", foreground="#334e68", font=("Segoe UI", 9, "bold"))
        style.map("Treeview", background=[("selected", "#d9eafd")], foreground=[("selected", "#102a43")])
        style.configure("Accent.TButton", background="#1769aa", foreground="#ffffff", font=("Segoe UI", 9, "bold"), padding=(8, 5))
        style.map("Accent.TButton", background=[("active", "#0f568f")])
        style.configure("TButton", font=("Segoe UI", 9), padding=(6, 4))

    def _build_interface(self) -> None:
        container = ttk.Frame(self.root, style="App.TFrame", padding=15)
        container.pack(fill="both", expand=True)
        container.columnconfigure(0, weight=1)

        # Header Row
        header_frame = ttk.Frame(container, style="App.TFrame")
        header_frame.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        header_frame.columnconfigure(0, weight=1)

        ttk.Label(header_frame, text="Airline Booking System", style="Title.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(header_frame, text="Techniques: Array | Stack | Priority Queue (Heap) + Waitlist (FIFO) | Linked List | BST | Graph (BFS/Dijkstra) | QuickSort | Hash Table | Seat Map | E-Ticket", style="Subtitle.TLabel").grid(row=1, column=0, sticky="w")

        # Admin Mode Toggle
        ttk.Checkbutton(
            header_frame, text="Admin Mode", variable=self.is_admin_mode, command=self._toggle_admin_mode
        ).grid(row=0, column=1, rowspan=2, sticky="e")

        # Search Bar & Route Finding Frame
        top_card = ttk.Frame(container, style="Card.TFrame", padding=10)
        top_card.grid(row=1, column=0, sticky="ew", pady=(0, 10))
        top_card.columnconfigure(1, weight=1)
        top_card.columnconfigure(3, weight=1)

        # Real-time Filter
        ttk.Label(top_card, text="Search Filter:", style="Section.TLabel").grid(row=0, column=0, padx=(0, 5))
        self.search_entry = ttk.Entry(top_card, width=20)
        self.search_entry.grid(row=0, column=1, sticky="w", padx=(0, 20))
        self.search_entry.bind("<KeyRelease>", self._on_search_filter)

        # Route Finder
        ttk.Label(top_card, text="Graph Search (From/To):", style="Section.TLabel").grid(row=0, column=2, padx=(0, 5))
        self.route_start = ttk.Entry(top_card, width=12)
        self.route_start.grid(row=0, column=3, sticky="w")
        self.route_end = ttk.Entry(top_card, width=12)
        self.route_end.grid(row=0, column=4, sticky="w", padx=5)

        ttk.Button(top_card, text="Fewest Stops", command=self._search_bfs_route).grid(row=0, column=5, padx=2)
        ttk.Button(top_card, text="Cheapest Route", command=self._search_dijkstra_route).grid(row=0, column=6, padx=2)

        # Flight Catalog Table (BST + QuickSort)
        flight_card = ttk.Frame(container, style="Card.TFrame", padding=12)
        flight_card.grid(row=2, column=0, sticky="nsew", pady=(0, 10))
        flight_card.columnconfigure(0, weight=1)

        ttk.Label(flight_card, text="Flight Catalog (Click header to QuickSort | Double click for Seat Map)", style="Section.TLabel").grid(row=0, column=0, sticky="w")

        self.flight_table = ttk.Treeview(
            flight_card,
            columns=("flight", "route", "departure", "price", "duration", "seats"),
            show="headings",
            selectmode="browse",
            height=4,
        )

        headers = [
            ("flight", "Flight #", 90),
            ("route", "Route", 280),
            ("departure", "Departure", 110),
            ("price", "Fare (₱)", 110),
            ("duration", "Duration", 100),
            ("seats", "Available Seats", 120)
        ]
        for col_id, title, w in headers:
            self.flight_table.heading(col_id, text=title, command=lambda c=col_id: self._sort_catalog_by(c))
            self.flight_table.column(col_id, width=w, anchor="w")

        self.flight_table.grid(row=1, column=0, sticky="nsew", pady=(5, 10))
        self.flight_table.bind("<Double-1>", self._open_seat_map_picker)

        # Booking Request Form
        form = ttk.Frame(flight_card, style="Card.TFrame")
        form.grid(row=2, column=0, sticky="ew")
        form.columnconfigure(1, weight=1)

        ttk.Label(form, text="Passenger:", style="CardText.TLabel").grid(row=0, column=0, padx=(0, 5))
        self.passenger_name = ttk.Entry(form)
        self.passenger_name.grid(row=0, column=1, sticky="ew", padx=(0, 10))

        ttk.Label(form, text="Class Tier:", style="CardText.TLabel").grid(row=0, column=2, padx=(0, 5))
        self.class_tier = ttk.Combobox(form, values=["VIP", "Business", "Economy"], width=10, state="readonly")
        self.class_tier.set("Economy")
        self.class_tier.grid(row=0, column=3, padx=(0, 10))

        ttk.Button(form, text="Pick Seat Grid", command=self._open_seat_map_picker).grid(row=0, column=4, padx=(0, 5))
        ttk.Label(form, textvariable=self.selected_seat_code, font=("Segoe UI", 9, "bold"), foreground="#1769aa").grid(row=0, column=5, padx=(0, 10))

        ttk.Button(form, text="Enqueue Request (Priority Queue)", style="Accent.TButton", command=self._queue_booking).grid(row=0, column=6)

        # Lower Split Frame (Queue & Bookings)
        lower = ttk.Frame(container, style="App.TFrame")
        lower.grid(row=3, column=0, sticky="nsew")
        lower.columnconfigure(0, weight=1)
        lower.columnconfigure(1, weight=1)

        # Pending Queue Card (Max Heap)
        queue_card = ttk.Frame(lower, style="Card.TFrame", padding=12)
        queue_card.grid(row=0, column=0, sticky="nsew", padx=(0, 5))
        queue_card.columnconfigure(0, weight=1)

        ttk.Label(queue_card, text="Priority Request Queue (Max Heap by Tier)", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        self.queue_table = ttk.Treeview(queue_card, columns=("priority", "passenger", "tier", "flight", "seat"), show="headings", height=5)
        for col, title, w in (("priority", "Score", 55), ("passenger", "Passenger", 150), ("tier", "Tier", 80), ("flight", "Flight", 75), ("seat", "Seat", 65)):
            self.queue_table.heading(col, text=title)
            self.queue_table.column(col, width=w, anchor="w")
        self.queue_table.grid(row=1, column=0, sticky="nsew", pady=(5, 5))

        queue_btn_bar = ttk.Frame(queue_card, style="Card.TFrame")
        queue_btn_bar.grid(row=2, column=0, sticky="ew")
        ttk.Button(queue_btn_bar, text="View Waitlist", command=self._show_waitlist).pack(side="left", padx=2)
        ttk.Button(queue_btn_bar, text="Process Highest Priority Queue", style="Accent.TButton", command=self._process_queue).pack(side="right", padx=2)

        # Bookings Card (Singly Linked List & Hash Table)
        bookings_card = ttk.Frame(lower, style="Card.TFrame", padding=12)
        bookings_card.grid(row=0, column=1, sticky="nsew", padx=(5, 0))
        bookings_card.columnconfigure(0, weight=1)

        ttk.Label(bookings_card, text="Confirmed Bookings (Singly Linked List & Hash Table)", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        self.booking_table = ttk.Treeview(bookings_card, columns=("id", "passenger", "tier", "flight", "seat", "fare"), show="headings", height=5)
        for col, title, w in (("id", "ID", 40), ("passenger", "Passenger", 130), ("tier", "Tier", 70), ("flight", "Flight", 65), ("seat", "Seat", 55), ("fare", "Fare", 80)):
            self.booking_table.heading(col, text=title)
            self.booking_table.column(col, width=w, anchor="w")
        self.booking_table.grid(row=1, column=0, sticky="nsew", pady=(5, 5))

        btn_bar = ttk.Frame(bookings_card, style="Card.TFrame")
        btn_bar.grid(row=2, column=0, sticky="ew")

        ttk.Button(btn_bar, text="Print Boarding Pass E-Ticket", command=self._print_e_ticket).pack(side="left", padx=2)
        ttk.Button(btn_bar, text="Cancel Selected Booking", command=self._cancel_selected_booking).pack(side="left", padx=2)
        ttk.Button(btn_bar, text="Undo Booking (LIFO Stack)", command=self._undo_last_booking).pack(side="right", padx=2)

        # Admin Panel Card
        self.admin_card = ttk.Frame(container, style="Card.TFrame", padding=10)
        self.admin_card.grid(row=4, column=0, sticky="ew", pady=(10, 0))
        self.admin_card.grid_remove()

        ttk.Label(self.admin_card, text="Admin Operations Control", style="Section.TLabel").grid(row=0, column=0, columnspan=6, sticky="w", pady=(0, 5))

        ttk.Button(self.admin_card, text="Reset System & Flush JSON Data", command=self._reset_system_data).grid(row=1, column=0, padx=5)

        # Status Bar
        ttk.Label(container, textvariable=self.status_text, style="Subtitle.TLabel").grid(row=5, column=0, sticky="w", pady=(10, 0))

    def _refresh_tables(self, filtered_flights=None, filtered_bookings=None) -> None:
        for t in (self.flight_table, self.queue_table, self.booking_table):
            t.delete(*t.get_children())

        flights_to_show = filtered_flights if filtered_flights is not None else self.system.flights
        for f in flights_to_show:
            self.flight_table.insert("", "end", iid=f.flight_number, values=(
                f.flight_number,
                f"{f.origin} -> {f.destination}",
                f.departure_time,
                f"₱{f.price:,.2f}",
                f"{f.duration_mins} mins",
                f"{f.available_seats}/{f.capacity}"
            ))

        for req in self.system.pending_requests:
            seat_str = req.requested_seat if req.requested_seat else "Auto"
            self.queue_table.insert("", "end", values=(
                -req.priority_score,
                req.passenger.name,
                req.passenger.ticket_class,
                req.flight_number,
                seat_str
            ))

        bookings_to_show = filtered_bookings if filtered_bookings is not None else self.system.bookings
        for b in bookings_to_show:
            self.booking_table.insert("", "end", values=(
                b.booking_id,
                b.passenger.name,
                b.passenger.ticket_class,
                b.flight_number,
                b.seat_number,
                f"₱{b.fare:,.2f}"
            ))

    def _toggle_admin_mode(self) -> None:
        if self.is_admin_mode.get():
            self.admin_card.grid()
            self.status_text.set("Admin mode enabled: Admin controls unlocked.")
        else:
            self.admin_card.grid_remove()
            self.status_text.set("Agent mode enabled.")

    def _on_search_filter(self, _event=None) -> None:
        query = self.search_entry.get().strip().lower()
        if not query:
            self._refresh_tables()
            return

        filtered_flights = [f for f in self.system.flights if query in f.flight_number.lower() or query in f.origin.lower() or query in f.destination.lower()]
        filtered_bookings = [b for b in self.system.bookings if query in b.passenger.name.lower() or query in b.flight_number.lower()]

        self._refresh_tables(filtered_flights=filtered_flights, filtered_bookings=filtered_bookings)
        self.status_text.set(f"Search filter applied for '{query}'.")

    def _sort_catalog_by(self, col_id: str) -> None:
        reverse = self.sort_state["reverse"] if self.sort_state["col"] == col_id else False
        self.sort_state = {"col": col_id, "reverse": not reverse}

        sorted_flights = self.system.sort_flights(col_id, reverse=not reverse)
        self._refresh_tables(filtered_flights=sorted_flights)
        self.status_text.set(f"Catalog sorted via QuickSort O(n log n) by {col_id} ({'Descending' if not reverse else 'Ascending'}).")

    def _open_seat_map_picker(self, _event=None) -> None:
        selection = self.flight_table.selection()
        if not selection:
            messagebox.showwarning("Seat Map", "Select a flight from the catalog table first.")
            return
        flight = self.system.search_flight_bst(selection[0])
        if not flight:
            return

        def on_selected(seat_code):
            self.selected_seat_code.set(f"Seat: {seat_code}")
            self.status_text.set(f"Picked seat {seat_code} for {flight.flight_number}.")

        SeatPickerWindow(self.root, flight, on_selected)

    def _search_bfs_route(self) -> None:
        start, end = self.route_start.get(), self.route_end.get()
        if not start or not end:
            messagebox.showwarning("BFS Search", "Enter both origin and destination cities.")
            return
        path = self.system.find_city_route_bfs(start, end)
        if path:
            route_str = " -> ".join(path)
            self.status_text.set(f"BFS Route Found: {route_str}")
            messagebox.showinfo("Unweighted BFS Route", f"Shortest Flight Leg Route:\n{route_str}")
        else:
            messagebox.showwarning("BFS Search", f"No route path found between {start} and {end}.")

    def _search_dijkstra_route(self) -> None:
        start, end = self.route_start.get(), self.route_end.get()
        if not start or not end:
            messagebox.showwarning("Dijkstra Search", "Enter both origin and destination cities.")
            return
        res = self.system.find_cheapest_route_dijkstra(start, end)
        if res:
            path, total_cost, flight_nos = res
            route_str = " -> ".join(path)
            flights_str = ", ".join(flight_nos)
            self.status_text.set(f"Dijkstra Cheapest Route: {route_str} (Total: ₱{total_cost:,.2f})")
            messagebox.showinfo("Dijkstra Algorithm Result", f"Cheapest Connected Route:\n{route_str}\n\nFlights: {flights_str}\nTotal Cost: ₱{total_cost:,.2f}")
        else:
            messagebox.showwarning("Dijkstra Search", f"No connecting route found between {start} and {end}.")

    def _queue_booking(self) -> None:
        selection = self.flight_table.selection()
        if not selection:
            messagebox.showwarning("Queue Request", "Select a flight from the table before enqueueing.")
            return
        pass_name = self.passenger_name.get().strip()
        if not pass_name:
            messagebox.showwarning("Queue Request", "Enter a valid passenger name.")
            return

        tier = self.class_tier.get()
        seat_raw = self.selected_seat_code.get().replace("Seat: ", "").strip()
        seat_code = seat_raw if seat_raw else None

        try:
            self.system.enqueue_booking(pass_name, selection[0], tier, seat_code)
        except ValueError as err:
            messagebox.showerror("Queue Error", str(err))
            return

        self.passenger_name.delete(0, "end")
        self.selected_seat_code.set("")
        self._refresh_tables()
        self.status_text.set(f"Enqueued {pass_name} ({tier} Class) in Priority Max Heap.")

    def _process_queue(self) -> None:
        results = self.system.process_booking_queue()
        self._refresh_tables()
        if not results:
            messagebox.showinfo("Process Queue", "Priority Queue is currently empty.")
            return
        self.status_text.set(f"Processed {len(results)} request(s) by priority level.")
        messagebox.showinfo("Priority Queue Processed", "\n".join(results))

    def _undo_last_booking(self) -> None:
        result = self.system.undo_last_booking()
        if not result:
            messagebox.showinfo("Undo", "No confirmed bookings in stack to undo.")
            return
        booking, notes = result
        self._refresh_tables()
        self.status_text.set(f"Popped booking #{booking.booking_id} ({booking.passenger.name}) from LIFO Stack.")
        extra = ("\n\n" + "\n".join(notes)) if notes else ""
        messagebox.showinfo("Booking Undone", f"Undone booking #{booking.booking_id} for {booking.passenger.name}.{extra}")

    def _cancel_selected_booking(self) -> None:
        selection = self.booking_table.selection()
        if not selection:
            messagebox.showwarning("Cancel", "Select a confirmed booking from the table.")
            return
        booking_id = int(self.booking_table.item(selection[0], "values")[0])
        if not messagebox.askyesno("Confirm Cancel", f"Cancel booking #{booking_id}? This cannot be undone."):
            return

        result = self.system.cancel_booking(booking_id)
        if not result:
            return
        booking, notes = result
        self._refresh_tables()
        self.status_text.set(f"Cancelled booking #{booking.booking_id} ({booking.passenger.name}).")
        extra = ("\n\n" + "\n".join(notes)) if notes else ""
        messagebox.showinfo(
            "Booking Cancelled",
            f"Booking #{booking.booking_id} cancelled. Seat {booking.seat_number} released.{extra}"
        )

    def _show_waitlist(self) -> None:
        entries = self.system.waitlist_entries
        if not entries:
            messagebox.showinfo("Waitlist", "No one is on the waitlist.")
            return
        lines = [
            f"{flight} | {'Any seat' if seat == 'ANY' else 'Seat ' + seat} | "
            f"#{pos} {req.passenger.name} ({req.passenger.ticket_class})"
            for flight, seat, pos, req in entries
        ]
        messagebox.showinfo("Waitlist (FIFO Queues)", "\n".join(lines))

    def _print_e_ticket(self) -> None:
        selection = self.booking_table.selection()
        if not selection:
            messagebox.showwarning("E-Ticket", "Select a confirmed booking from the table.")
            return
        item_vals = self.booking_table.item(selection[0], "values")
        booking_id = int(item_vals[0])

        matching_bookings = [b for b in self.system.bookings if b.booking_id == booking_id]
        if not matching_bookings:
            return

        filename = self.system.generate_e_ticket(matching_bookings[0])
        self.status_text.set(f"Generated E-Boarding Pass ticket file: {filename}")
        messagebox.showinfo("E-Ticket Generated", f"Boarding pass ticket exported to:\n{filename}")

    def _reset_system_data(self) -> None:
        if messagebox.askyesno("Confirm Reset", "Are you sure you want to reset all booking data and clear bookings.json?"):
            self.system.reset_system_data()
            self._refresh_tables()
            self.status_text.set("System data reset successfully.")


def create_initial_flights() -> list[Flight]:
    return [
        Flight("PH101", "Manila", "Cebu", "08:30", 20, 2500.0, 75),
        Flight("PH205", "Cebu", "Davao", "11:15", 20, 1800.0, 60),
        Flight("PH310", "Manila", "Puerto Princesa", "14:00", 20, 3200.0, 90),
        Flight("PH402", "Davao", "Manila", "17:45", 20, 2900.0, 110),
        Flight("PH500", "Manila", "Davao", "06:00", 20, 5000.0, 105),
    ]


def main() -> None:
    root = tk.Tk()
    sys = AirlineBookingSystem(create_initial_flights())
    AirlineBookingApp(root, sys)
    root.mainloop()


if __name__ == "__main__":
    main()