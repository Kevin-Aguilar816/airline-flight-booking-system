"""A desktop airline booking system incorporating complete Data Structure techniques:
- Array / List (Flight catalog & tabular data)
- Stack (LIFO for booking undo operations)
- Queue (FIFO for passenger booking requests)
- Singly Linked List (Node-based storage for confirmed bookings)
- Binary Search Tree / BST (O(log n) flight lookup by flight number)
- Graph (Adjacency List representation of airport cities & flight routes with BFS route finding)
"""

from collections import deque
from dataclasses import dataclass
from itertools import count
import json
from pathlib import Path
import tkinter as tk
from tkinter import messagebox, ttk


# ============================================================================
# 1. DATA MODELS & PRIMITIVE STRUCTURES (Module 1)
# ============================================================================

@dataclass
class Flight:
    """A flight record with capacity management."""
    flight_number: str
    origin: str
    destination: str
    departure_time: str
    capacity: int
    booked_seats: int = 0

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

    def reserve_seat(self) -> str:
        if self.available_seats <= 0:
            raise ValueError(f"Flight {self.flight_number} is fully booked.")
        self.booked_seats += 1
        return f"{self.flight_number}-{self.booked_seats:03d}"


@dataclass(frozen=True)
class Passenger:
    """Passenger entity structure."""
    name: str

    def __post_init__(self) -> None:
        if not self.name.strip():
            raise ValueError("Passenger name cannot be empty.")


@dataclass(frozen=True)
class BookingRequest:
    """FIFO Queue element representing an incoming booking request."""
    passenger: Passenger
    flight_number: str


@dataclass(frozen=True)
class Booking:
    """Confirmed booking record stored in dynamic data structures."""
    booking_id: int
    passenger: Passenger
    flight_number: str
    seat_number: str


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
# 4. TREE DATA STRUCTURE (Module 4 & 6: Binary Search Tree / BST)
# ============================================================================

class BSTNode:
    """Binary Search Tree Node for Flight indexing."""
    def __init__(self, flight: Flight) -> None:
        self.flight: Flight = flight
        self.left: BSTNode | None = None
        self.right: BSTNode | None = None


class FlightBST:
    """Binary Search Tree for O(log n) flight searching by flight number."""
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
# 5. GRAPH DATA STRUCTURE (Module 5: Adjacency List & BFS Traversal)
# ============================================================================

class FlightGraph:
    """Graph representing airport routes (Vertices = Cities, Edges = Flights)."""
    def __init__(self) -> None:
        self.adj_list: dict[str, list[tuple[str, str]]] = {}

    def add_route(self, origin: str, destination: str, flight_number: str) -> None:
        if origin not in self.adj_list:
            self.adj_list[origin] = []
        if destination not in self.adj_list:
            self.adj_list[destination] = []
        self.adj_list[origin].append((destination, flight_number))

    def find_route_bfs(self, start: str, end: str) -> list[str] | None:
        """Breadth-First Search (BFS) to find the shortest route between cities."""
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

            for neighbor, _ in self.adj_list.get(node, []):
                if neighbor not in visited:
                    visited.add(neighbor)
                    new_path = list(path)
                    new_path.append(neighbor)
                    queue.append(new_path)

        return None


# ============================================================================
# 6. MAIN SYSTEM MANAGER
# ============================================================================

class AirlineBookingSystem:
    """Central system integrating Array, Stack, Queue, Linked List, BST, and Graph."""

    def __init__(self, flights: list[Flight]) -> None:
        if not flights:
            raise ValueError("At least one flight must be provided.")

        self._flights_list: list[Flight] = flights  # Array / List
        self._flight_bst = FlightBST()              # Tree (BST)
        self._flight_graph = FlightGraph()          # Graph

        for flight in flights:
            self._flight_bst.insert(flight)
            self._flight_graph.add_route(flight.origin, flight.destination, flight.flight_number)

        self._booking_queue: deque[BookingRequest] = deque()  # Queue (FIFO)
        self._bookings_linked_list = SinglyLinkedList()       # Linked List
        self._booking_stack = Stack()                         # Stack (LIFO)
        self._booking_ids = count(1)
        self.load_from_json()

    @property
    def flights(self) -> tuple[Flight, ...]:
        return tuple(self._flight_bst.get_all_flights())

    @property
    def pending_requests(self) -> tuple[BookingRequest, ...]:
        return tuple(self._booking_queue)

    @property
    def bookings(self) -> tuple[Booking, ...]:
        return tuple(self._bookings_linked_list.to_list())

    def search_flight_bst(self, flight_number: str) -> Flight | None:
        """Search flight using BST."""
        return self._flight_bst.search(flight_number)

    def find_city_route_bfs(self, origin: str, destination: str) -> list[str] | None:
        """Find route path using Graph BFS."""
        return self._flight_graph.find_route_bfs(origin, destination)

    def save_to_json(self, filepath: str = "bookings.json") -> None:
        data = [
            {
                "booking_id": b.booking_id,
                "passenger_name": b.passenger.name,
                "flight_number": b.flight_number,
                "seat_number": b.seat_number,
            }
            for b in self.bookings
        ]
        with open(filepath, "w") as file:
            json.dump(data, file, indent=4)

    def load_from_json(self, filepath: str = "bookings.json") -> None:
        path = Path(filepath)
        if not path.exists():
            return

        with open(filepath, "r") as file:
            data = json.load(file)

        max_id = 0
        for item in data:
            flight = self.search_flight_bst(item["flight_number"])
            if flight and flight.available_seats > 0:
                flight.booked_seats += 1
                booking = Booking(
                    booking_id=item["booking_id"],
                    passenger=Passenger(item["passenger_name"]),
                    flight_number=item["flight_number"],
                    seat_number=item["seat_number"],
                )
                self._bookings_linked_list.append(booking)
                self._booking_stack.push(booking)
                if item["booking_id"] > max_id:
                    max_id = item["booking_id"]

        self._booking_ids = count(max_id + 1)

    def queue_booking(self, passenger_name: str, flight_number: str) -> None:
        flight_number = flight_number.strip().upper()
        flight = self.search_flight_bst(flight_number)
        if not flight:
            raise ValueError(f"Unknown flight number: {flight_number}")

        passenger = Passenger(passenger_name.strip())
        self._booking_queue.append(BookingRequest(passenger, flight_number))

    def process_booking_queue(self) -> list[str]:
        results = []
        while self._booking_queue:
            request = self._booking_queue.popleft()
            flight = self.search_flight_bst(request.flight_number)
            if not flight or flight.available_seats == 0:
                results.append(
                    f"Could not book {request.passenger.name} on "
                    f"{request.flight_number}: flight unavailable or full."
                )
                continue

            seat_number = flight.reserve_seat()
            booking = Booking(
                booking_id=next(self._booking_ids),
                passenger=request.passenger,
                flight_number=flight.flight_number,
                seat_number=seat_number,
            )
            self._bookings_linked_list.append(booking)
            self._booking_stack.push(booking)
            results.append(
                f"Confirmed booking #{booking.booking_id} for "
                f"{booking.passenger.name} on {booking.flight_number}; "
                f"seat {booking.seat_number}."
            )
        self.save_to_json()
        return results

    def undo_last_booking(self) -> Booking | None:
        booking = self._booking_stack.pop()
        if booking is None:
            return None

        self._bookings_linked_list.remove(booking)
        flight = self.search_flight_bst(booking.flight_number)
        if flight:
            flight.booked_seats -= 1

        self.save_to_json()
        return booking


# ============================================================================
# 7. TKINTER USER INTERFACE
# ============================================================================

class AirlineBookingApp:
    """Tkinter interface for desktop flight booking desk."""

    def __init__(self, root: tk.Tk, system: AirlineBookingSystem) -> None:
        self.root = root
        self.system = system
        self.status_text = tk.StringVar(value="System initialized with all Data Structure techniques.")

        self.root.title("Airline Booking System (Data Structures Edition)")
        self.root.geometry("1100x800")
        self.root.minsize(900, 650)
        self.root.configure(background="#f3f6fb")

        self._configure_styles()
        self._build_interface()
        self._refresh_tables()

    def _configure_styles(self) -> None:
        style = ttk.Style(self.root)
        style.theme_use("clam")
        style.configure("App.TFrame", background="#f3f6fb")
        style.configure("Card.TFrame", background="#ffffff")
        style.configure("Title.TLabel", background="#f3f6fb", foreground="#102a43", font=("Segoe UI", 22, "bold"))
        style.configure("Subtitle.TLabel", background="#f3f6fb", foreground="#52667a", font=("Segoe UI", 10))
        style.configure("Section.TLabel", background="#ffffff", foreground="#102a43", font=("Segoe UI", 11, "bold"))
        style.configure("CardText.TLabel", background="#ffffff", foreground="#52667a", font=("Segoe UI", 9))
        style.configure("Treeview", rowheight=28, background="#ffffff", fieldbackground="#ffffff", foreground="#243b53", font=("Segoe UI", 9))
        style.configure("Treeview.Heading", background="#eaf0f7", foreground="#334e68", font=("Segoe UI", 9, "bold"))
        style.map("Treeview", background=[("selected", "#d9eafd")], foreground=[("selected", "#102a43")])
        style.configure("Accent.TButton", background="#1769aa", foreground="#ffffff", font=("Segoe UI", 9, "bold"), padding=(10, 6))
        style.map("Accent.TButton", background=[("active", "#0f568f")])
        style.configure("TButton", font=("Segoe UI", 9), padding=(8, 5))

    def _build_interface(self) -> None:
        container = ttk.Frame(self.root, style="App.TFrame", padding=20)
        container.pack(fill="both", expand=True)
        container.columnconfigure(0, weight=1)

        # Header
        ttk.Label(container, text="Airline Booking Desk", style="Title.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(container, text="Data Structures: Array | Stack | Queue | Singly Linked List | BST | Graph", style="Subtitle.TLabel").grid(row=1, column=0, sticky="w", pady=(0, 10))

        # Graph Search Frame
        graph_card = ttk.Frame(container, style="Card.TFrame", padding=12)
        graph_card.grid(row=2, column=0, sticky="ew", pady=(0, 10))
        graph_card.columnconfigure(1, weight=1)
        graph_card.columnconfigure(3, weight=1)

        ttk.Label(graph_card, text="Graph Route Search (BFS):", style="Section.TLabel").grid(row=0, column=0, padx=(0, 10))
        ttk.Label(graph_card, text="From:", style="CardText.TLabel").grid(row=0, column=1, sticky="e")
        self.route_start = ttk.Entry(graph_card, width=15)
        self.route_start.grid(row=0, column=2, padx=5)

        ttk.Label(graph_card, text="To:", style="CardText.TLabel").grid(row=0, column=3, sticky="e")
        self.route_end = ttk.Entry(graph_card, width=15)
        self.route_end.grid(row=0, column=4, padx=5)

        ttk.Button(graph_card, text="Find Route Path", command=self._search_graph_route).grid(row=0, column=5, padx=(10, 0))

        # Flights Card
        flight_card = ttk.Frame(container, style="Card.TFrame", padding=14)
        flight_card.grid(row=3, column=0, sticky="nsew", pady=(0, 10))
        flight_card.columnconfigure(0, weight=1)

        ttk.Label(flight_card, text="Available Flights (Indexed via BST)", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        
        self.flight_table = ttk.Treeview(
            flight_card,
            columns=("flight", "route", "departure", "seats"),
            show="headings",
            selectmode="browse",
            height=4,
        )
        for col, title, w in (("flight", "Flight", 110), ("route", "Route", 400), ("departure", "Departure", 150), ("seats", "Seats Available", 150)):
            self.flight_table.heading(col, text=title)
            self.flight_table.column(col, width=w, anchor="w")
        self.flight_table.grid(row=1, column=0, sticky="nsew", pady=(5, 10))

        # Queue Booking Form
        form = ttk.Frame(flight_card, style="Card.TFrame")
        form.grid(row=2, column=0, sticky="ew")
        form.columnconfigure(1, weight=1)

        ttk.Label(form, text="Passenger Name:", style="CardText.TLabel").grid(row=0, column=0, sticky="w", padx=(0, 8))
        self.passenger_name = ttk.Entry(form)
        self.passenger_name.grid(row=0, column=1, sticky="ew", padx=(0, 10))
        self.passenger_name.bind("<Return>", self._queue_booking)

        ttk.Button(form, text="Enqueue Request (FIFO)", style="Accent.TButton", command=self._queue_booking).grid(row=0, column=2)

        # Lower Split Frame
        lower = ttk.Frame(container, style="App.TFrame")
        lower.grid(row=4, column=0, sticky="nsew")
        lower.columnconfigure(0, weight=1)
        lower.columnconfigure(1, weight=1)

        # Queue Card
        queue_card = ttk.Frame(lower, style="Card.TFrame", padding=14)
        queue_card.grid(row=0, column=0, sticky="nsew", padx=(0, 5))
        queue_card.columnconfigure(0, weight=1)

        ttk.Label(queue_card, text="Pending Queue (FIFO Queue)", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        self.queue_table = ttk.Treeview(queue_card, columns=("pos", "passenger", "flight"), show="headings", height=5)
        for col, title, w in (("pos", "#", 40), ("passenger", "Passenger", 180), ("flight", "Flight", 90)):
            self.queue_table.heading(col, text=title)
            self.queue_table.column(col, width=w, anchor="w")
        self.queue_table.grid(row=1, column=0, sticky="nsew", pady=(5, 5))

        ttk.Button(queue_card, text="Process Queue", style="Accent.TButton", command=self._process_queue).grid(row=2, column=0, sticky="e")

        # Bookings Card
        bookings_card = ttk.Frame(lower, style="Card.TFrame", padding=14)
        bookings_card.grid(row=0, column=1, sticky="nsew", padx=(5, 0))
        bookings_card.columnconfigure(0, weight=1)

        ttk.Label(bookings_card, text="Confirmed Bookings (Singly Linked List)", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        self.booking_table = ttk.Treeview(bookings_card, columns=("id", "passenger", "flight", "seat"), show="headings", height=5)
        for col, title, w in (("id", "ID", 45), ("passenger", "Passenger", 160), ("flight", "Flight", 80), ("seat", "Seat", 90)):
            self.booking_table.heading(col, text=title)
            self.booking_table.column(col, width=w, anchor="w")
        self.booking_table.grid(row=1, column=0, sticky="nsew", pady=(5, 5))

        ttk.Button(bookings_card, text="Undo Last Booking (LIFO Stack)", command=self._undo_last_booking).grid(row=2, column=0, sticky="e")

        # Status Bar
        ttk.Label(container, textvariable=self.status_text, style="Subtitle.TLabel").grid(row=5, column=0, sticky="w", pady=(10, 0))

    def _refresh_tables(self) -> None:
        for t in (self.flight_table, self.queue_table, self.booking_table):
            t.delete(*t.get_children())

        for f in self.system.flights:
            self.flight_table.insert("", "end", iid=f.flight_number, values=(f.flight_number, f"{f.origin} to {f.destination}", f.departure_time, f"{f.available_seats}/{f.capacity}"))

        for pos, req in enumerate(self.system.pending_requests, start=1):
            self.queue_table.insert("", "end", values=(pos, req.passenger.name, req.flight_number))

        for b in self.system.bookings:
            self.booking_table.insert("", "end", values=(b.booking_id, b.passenger.name, b.flight_number, b.seat_number))

    def _search_graph_route(self) -> None:
        start = self.route_start.get()
        end = self.route_end.get()
        if not start or not end:
            messagebox.showwarning("Route Search", "Please enter both origin and destination cities.")
            return
        path = self.system.find_city_route_bfs(start, end)
        if path:
            route_str = " -> ".join(path)
            self.status_text.set(f"Graph BFS Route Found: {route_str}")
            messagebox.showinfo("Route Found (Graph BFS)", f"Connected Route Path:\n{route_str}")
        else:
            self.status_text.set(f"No connected route found between {start} and {end}.")
            messagebox.showwarning("Route Search", f"No connecting flight path found between {start} and {end}.")

    def _queue_booking(self, _event: tk.Event | None = None) -> None:
        selection = self.flight_table.selection()
        if not selection:
            messagebox.showwarning("Select Flight", "Choose a flight from the table before adding a request.")
            return
        try:
            self.system.queue_booking(self.passenger_name.get(), selection[0])
        except ValueError as err:
            messagebox.showerror("Error", str(err))
            return
        self.passenger_name.delete(0, "end")
        self._refresh_tables()
        self.status_text.set("Booking request enqueued in FIFO queue.")

    def _process_queue(self) -> None:
        results = self.system.process_booking_queue()
        self._refresh_tables()
        if not results:
            self.status_text.set("No requests in queue.")
            return
        self.status_text.set(f"Processed {len(results)} request(s). Saved to JSON & Linked List.")
        messagebox.showinfo("Queue Processed", "\n".join(results))

    def _undo_last_booking(self) -> None:
        booking = self.system.undo_last_booking()
        if not booking:
            self.status_text.set("Nothing to undo.")
            messagebox.showinfo("Undo", "No confirmed bookings to undo.")
            return
        self._refresh_tables()
        self.status_text.set(f"Popped booking #{booking.booking_id} from LIFO Stack.")
        messagebox.showinfo("Undone", f"Booking #{booking.booking_id} for {booking.passenger.name} undone.")


def create_booking_system() -> AirlineBookingSystem:
    return AirlineBookingSystem([
        Flight("PH101", "Manila", "Cebu", "08:30", 120),
        Flight("PH205", "Cebu", "Davao", "11:15", 100),
        Flight("PH310", "Manila", "Puerto Princesa", "14:00", 80),
        Flight("PH402", "Davao", "Manila", "17:45", 110),
    ])


def main() -> None:
    root = tk.Tk()
    AirlineBookingApp(root, create_booking_system())
    root.mainloop()


if __name__ == "__main__":
    main()